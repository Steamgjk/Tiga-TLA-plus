
`^\textbf{\large Tiga TLA+ Specification}\\^' 
 
------------------------------ MODULE Tiga ----------------------------------

EXTENDS Naturals, TLC, FiniteSets, Sequences

--------------------------------------------------------------------------------


(* `^\textbf{\large Bounds for Model Check [Configurable]}^' *)

\* Time Range [Configurable]
MaxTime == 3

\* In Tiga, we assume client and coordinator are co-located
\* In this spec, we use "coordinator" to represent them
\* Each coordinator is only allowed to submit MaxReqNum requests [Configurable]
\* In the specification, we will only consider two roles, client and replicas
\* (i.e. it can be considered as co-locating one proxy with one client)
\* For the proxy-based design, we just need to replace client with proxy, 
\* and then the specification describes the interaction between proxy and replicas
MaxReqNum == 1 

\* The leader is only allowed to crash when the view < MaxViews [Configurable]
MaxViews == 3

\* The set of replicas and an ordering of them [Can be configured in TLA+ Toolbox]
Replicas == 0..2
ReplicaOrder == <<0,1,2>>
Shards == 0..2
Coords == 0..1
LatencyBounds  == [ c \in Coords |->  1 ]

ASSUME  IsFiniteSet(Replicas) 
ASSUME  IsFiniteSet(Shards)
ASSUME ReplicaOrder \in Seq(Replicas)
Servers ==  {
    [
        replicaId |-> e[1],
        shardId |-> e[2]
    ]: e \in Replicas \X Shards
}

---------------------------------------------------------------------------
\* These variables are used to implment at-most-once primitives


(* `^\textbf{\large Constants}^' *)
F == (Cardinality(Replicas) - 1) \div 2
ceilHalfF == IF (F \div 2) * 2 = F THEN F \div 2 ELSE (F+1) \div 2
floorHalfF == F \div 2
QuorumSize == F + 1
FastQuorumSize == F + ceilHalfF + 1
RecoveryQuorumSize == ceilHalfF + 1
FastQuorums == {R \in SUBSET(Replicas) : 
                Cardinality(R) >= FastQuorumSize }
Quorums == {R \in SUBSET(Replicas) : 
                Cardinality(R) * 2 > Cardinality(Replicas)}   


(* `^\textbf{\large Server Status}^' *)
StNormal == 1
StViewChange == 2
StCrossShardSyncing == 3
StRecovering == 4
StFailing == 5


(* `^\textbf{\large Message Types}^' *)
MTxn == 1
MLogEntry == 2  \* Log entry, different from index, it includes command field, which can be large in practice
MTimestampNotification == 3 \* Leaders send the message to other leaders for timestamp agreement
MInterReplicaSync == 4   \* Synchronize within shard group (across replicas) to ensure strict serializability 
MFastReply == 5 \* Fast Reply Message
MSlowReply == 6 \* Slow Reply Message

\* The following messages are mainly for view change within each sharding group
MViewChangeReq == 7       \* Sent by config manager when leader/sequencer failure detected
MViewChange == 8        \* Sent to ACK view change
MStartView == 9           \* Sent by new leader to start view

\* The following messages are mainly used for periodic sync
\* Just as described in NOPaxos, it is an optional optimization to enable fast recovery after failure
MLocalSyncStatus == 10         \* Sent by the leader to ensure log durability
MLocalCommit == 11             \* Sent by followers as ACK
\* The following messages are used for periodic sync across sharding groups
\* This is an optional optimization to enable fast recovery
MPeerShardCommitStatus == 12


\* The following messages are mainly used for server recovery
MCrashVectorReq == 13
MCrashVectorRep == 14
MRecoveryReq == 15
MRecoveryRep == 16
MStartViewReq == 17
MCrossShardVerifyReq == 18
MCrossShardVerifyRep == 19

(*  Config Manager (CM)'s Operations. Since CM is supported by typical viewstamped replication (VR),  in this spec, we do not repeat the VR's failure recovery spec for CM
*)
MCMPrepare == 20
MCMPrepareReply == 21
MCMCommit == 22



(*
  `^\textbf{\large Message Schemas}^'

    Each server is identified by a combination of <replicaId, shardId>
    TxnID uniquely identifies one request on one server
    But across replicas, the same TxnID may have different timestamps
    (the leader may modify the timestamp to make the request eligible to enter the early-buffer)
    so <timestamp, txnId> uniquely identifes one request across replicas 

    TxnID = [
        coordId |-> i in (1..),
        rId     |-> i in (1..)
    ]

    Txn = [
        mtype   |-> MTxn
        txnId   |-> TxnID,
        shards  |-> Shards,
        command |-> command,
        st      |-> sendTime,
        bound   |-> latencyBound
    ]

    LogEntry = [
        mtype   |-> MLogEntry
        txnId   |-> TxnID,
        shards  |-> Shards,
        command |-> command,
        timestamp|-> timestamp
    ]

    After the request arrives at the shards and is placed into its early buffer (either with timestamp modified or not), the server will broadcast TimestampNotification to all the other servers in the same replica group to tell them the timestamp of the request on its own server

    TimestampNotification = [ 
        mtype   |-> MTimestampNotification,
        gView   |-> 0...x
        lView   |-> 0...y 
        sender  |-> src \in Servers,
        dest    |-> dst \in Servers,
        entry   |-> LogEntry
    ]

    After leader has released the txn, it synchornizes the log with its followers. If followers are inconsistent, they will rectify their logs to keey consistent with leader

    InterReplicaSync = [
        mtype       |-> MInterReplicaSync,
        lView       |-> 0...y
        sender      |-> src \in Servers,
        dest        |-> dst \in Servers,
        entries     |-> [LogEntry...]
    ]
  
    logId (i.e., the position index of the log entry in the log list) is not necessary and it is not described in the paper. Here we include logSlotNum in FastReply and SlowReply messages to facilitate the check of Linearizability invariant

    FastReply = [ 
        mtype       |-> MFastReply,
        sender      |-> src \in Servers,
        dest        |-> dst \in Coords,
        gView       |-> 0...x
        lView       |-> 0...x
        txnId       |->  txnId
        
        In real implementation, we use SHA1+Incremental Hash

        hash        |-> [ entries |-> log entries so far
                         cv |-> crashVector ] 
        timestamp    |-> i \in (1..MaxTime+MaxBound),
        logId       |-> n \in (1..)
    ]

    SlowReply = [ 
        mtype      |-> MSlowReply,
        sender     |-> src \in Servers,
        dest       |-> c \in Coords,
        gView      |-> 0...x
        lView      |-> 0...x
        txnId      |->  txnId
        logId      |-> n \in (1..)
    ]
      
      
    ViewChangeReq = [ 
        mtype   |-> MViewChangeReq,
        sender  |-> src \in Replicas, (by configManager)
        dest    |-> dst \in Servers,
        gView   |-> 0..x
        gVec    |-> the lViews for each shard
    ]

    ViewChange = [ 
        mtype       |-> MViewChange,
        sender      |-> src \in Servers,
        dest        |-> dst \in Servers,
        gView       |-> 0..x
        gVec        |-> the lViews for each shard
        lView       |-> 0..x
        lastNormal  |-> v \in ViewIDs,
        lSyncPoint  |-> 0..
        entries     |-> l \in vLogs[1..n],
        cv          |-> crash vector  
    ]

    Tell the leaders in other sharding groups my syncPoint

    MCrossShardVerifyReq = [ 
        mtype      |-> MCrossShardVerifyReq,
        sender     |-> src \in Servers,
        dest       |-> dst \in Servers,
        lView      |-> 0..x
        gView      |-> 0..x
        syncedDdl  |-> The largest timestamp of the synced entries
    ]

    Reply the entries to the other leaders. These entries' log positions are beyond the syncPoint of the receiving leader, so that the receiving leader can verify whether it needs timestamp agreement for the txn, or even misses the txn 

    MCrossShardVerifyRep = [ 
        mtype      |-> MCrossShardVerifyRep,
        sender     |-> src \in Servers,
        dest       |-> dst \in Servers,
        lView      |-> 0..x
        gView      |-> 0..x
        entries    |-> l \in vLogs[1..n]
    ]

    StartView = [ 
        mtype      |-> MStartView,
        sender     |-> src \in Servers,
        dest       |-> dst \in Servers,
        lView      |-> 0...x
        gView      |-> 0...x
        gVec       |-> the lViews for each shard
        entries    |-> l \in vLogs[1..n],
        cv         |-> crash vector 
    ]


        
    CrashVectorReq = [ 
        mtype       |-> MCrashVectorReq,
        sender      |-> src \in Servers,
        dest        |-> dst \in Servers,
        nonce       |-> nonce
    ] 

    CrashVectorRep = [ 
        mtype         |-> MCrashVectorRep,
        sender        |-> src \in Servers,
        dest          |-> dst \in Servers,
        nonce         |-> nonce,
        cv            |-> vector of counters
    ] 
      
    RecoveryReq   = [ 
        mtype         |-> MRecoveryReq,
        sender        |-> src \in Servers,
        dest          |-> dst \in Servers,
        cv            |-> vector of counters
    ]  
      
    RecoveryRep   =[ 
        mtype   |-> MRecoveryRep,
        sender  |-> src \in Servers,
        dest    |-> dst \in Servers,
        gView   |-> 0..x
        lView   |-> 0..x
        cv      |-> vector of counters
    ]           

    StartViewReq  =[ 
        mtype       |-> MStartViewReq,
        sender      |-> src \in Servers,
        dest        |-> dst \in Servers,
        lView       |-> 0..x
        cv          |-> vector of counters
    ]  



    Follower reports to its leader
    
    LocalSyncStatus = [ 
        mtype       |-> MLocalSyncStatus,
        sender      |-> src \in Servers,
        dest        |-> dst \in Servers,
        lView       |-> 0...x
        lSyncPoint  |-> 1.. 
        cv          |-> vector of counters
    ]

    Leader notifies its followers
    
    LocalCommit = [ 
        mtype       |-> MLocalCommit,
        sender      |-> src \in Servers,
        dest        |-> dst \in Servers,
        lView       |-> 0...x
        entries     |-> log entries 
        lCommitPoint|-> n \in (1...)
    ]

    Each server tells its neighbors (the servers in the same region but belong to different shards) its local commit status. This is optional optimization (only for checkpoint and failure recovery acceleration)
    
    \* maybe obsolete
    PeerShardCommitStatus =[ 
        mtype       |-> MPeerShardCommitStatus,
        sender      |-> src \in Servers,
        dest        |-> dst \in Servers,
        gView       |-> 0..x
        timestamp    |-> the largest committed timestamp
    ]


    
    Configuration Manager (CM)'s message to prepare global information (including gView and gVec)
    
    In our implementation, CM is co-located on Shard-0, but from design perspective, CM is completed standalone and decoupled from Tiga Servers

    CMPrepare =[
        mtype   |-> MCMPrepare,
        sender  |-> src \in Servers,
        dest    |-> dst \in Servers,
        cView   |-> 0..x
        gView   |-> 0..x
        gVec    |-> [shardId |-> lView]
    ]

    CMPrepareReply = [
        mtype   |-> MCMPrepareReply,
        sender  |-> src \in Servers,
        dest    |-> dst \in Servers,
        cView   |-> 0..x
        gView   |-> 0..x
    ]

    CMCommit = [
        mtype   |-> MCMPrepareReply,
        sender  |-> src \in Servers,
        dest    |-> dst \in Servers,
        cView   |-> 0..x
        gView   |-> 0..x
    ]

*)

\* --------------------------------------------------------------------------------
\* (* `^\textbf{\large Variables}^' *)

\* `^\textbf{Network State}^'

VARIABLES messages \* Set of all messages sent

\* `^\textbf{Server State}^'
VARIABLES   
            (* Messages that have been processed by servers 
            *)
            vServerProcessed, 
            (* Log list of entries 
            *)
            vLog,            
            (* The sequencer to hold txns and release it after clock passes its timestamp (s+l) 
            *)
            vEarlyBuffer, 
            (* The buffer to hold txns on followers because these txns come too late and cannot enter early-buffer 
            *)
            vLateBuffer,     
            (* Each leader server has a data structure of TimestampQuroum to collect the timestamps from other servers for agreement 
            *)
            vTimestampQuorum,

            (* One of StNormal, StViewChange, StFailing, StCrossShardSyncing, StRecovering  
            *)
            vServerStatus,
            (* Global views of each server 
            *) 
            vGView,
            (* The g-vecs of each server 
            *)
            vGVec,
            (* Local views of each server 
            *)
            vLView,  
            (* Current Time of the server 
            *)
            vServerClock,   
            (* Last lView in which this server had StNormal status 
            *)
            vLastNormView,   
            (* Used for collecting view change votes 
            *)
            vViewChange,  
            (* Used for collecting CrossShardVerify replies. After the leader have recovered their logs for its own shard, they need verify from the other shards to ensure the recovered logs satisfy strict serializability, i.e., every log has commonly-agreed timestamps across sharding groups. 
            *)
            vCrossShardVerifyReps,
            (* vLSyncPoint indicates to which the server state (vLog) is consistent with the leader.  
            *)
            vLSyncPoint,
            (* vLCommitPoint indicates that the log entries before this point has been locally committed, i.e., replicated to majority in this sharding groups. So followers can safely execute the logged txns 
            *)
            vLCommitPoint, 
            (* vLSyncQuorum is used by each leader to collect the LocalSyncStatus messages from servers in the same sharding group 
            *)
            vLSyncQuorum,  
            (* Locally unique string (for CrashVectorReq) 
            *)          
            vUUIDCounter,   
            (* CrashVector, initialized as all-zero vector 
            *)
            vCrashVector,    
            vCrashVectorReps,
            vRecoveryReps


                    
\* `^\textbf{Coordinator State}^'

VARIABLES   (* Current Clock Time of the coordinator*)
            vCoordClock, 
            (* The txns that have been sent by this coordinator. This variable makes it easy to derive the Invariants 
            *) 
            vCoordTxns,
            (* Messages that have been processed by coordinators 
            *)
            vCoordProcessed



\* `^\textbf{Configuration Manager (CM) State}^'

VARIABLES   
            (* Since CM is supported by traditional VR, here we do not want to repeat VR's failure recovery in this spec, so we make CMStatus always StNormal
            *)
            vCMStatus, 
            vCMView,
            (* Config Manager: the latest global info the manager maintains (gView and gVec)
            *)
            vCMGInfo,
            vCMPrepareGInfo,
            (* Config Manager: quorum of CMPrepareReplies
            *)  
            vCMPrepareReps,

            vCMProcessed

VARIABLES  ActionName

networkVars == << messages >>

serverStateVars == 
    << vLog, vEarlyBuffer, vLateBuffer, 
    vTimestampQuorum, vCrossShardVerifyReps, vServerStatus, 
    vGView, vGVec, vLView, vServerClock, vLastNormView, 
    vViewChange, vLSyncPoint, vLCommitPoint, 
    vLSyncQuorum,vUUIDCounter, vCrashVector, 
    vCrashVectorReps, vRecoveryReps, vServerProcessed>>

coordStateVars == <<vCoordClock, vCoordTxns, vCoordProcessed>>

configManagerStateVars == << vCMStatus, vCMView, vCMGInfo, 
                            vCMPrepareGInfo, vCMPrepareReps, 
                            vCMProcessed >>


InitNetworkState == messages = {}

InitServerState ==
    /\  vServerProcessed = [ serverId \in Servers |-> {} ]
    /\  vLog = [ serverId \in Servers |-> << >> ]
    /\  vEarlyBuffer   = [ serverId \in Servers |-> {} ]
    /\  vLateBuffer   = [ serverId \in Servers |-> {} ]
    /\  vTimestampQuorum  =   [ serverId \in Servers |-> {} ]
    /\  vCrossShardVerifyReps = [ serverId \in Servers |-> {} ]
    /\  vServerStatus    =   [ serverId \in Servers |-> StNormal ]
    /\  vGView  =   [ serverId \in Servers |-> 0 ]
    /\  vGVec = [
            serverId \in Servers |-> [
                shardId \in Shards |->0
            ]
        ]
    /\  vLView  =   [ serverId \in Servers |-> 0 ]
    /\  vServerClock =   [ serverId \in Servers |-> 1 ]
    /\  vLastNormView    = [ serverId \in Servers |-> 0 ]
    /\  vViewChange = [ serverId \in Servers |-> {} ]
    /\  vLSyncPoint   = [ serverId \in Servers |-> 0 ]
    /\  vLCommitPoint   = [ serverId \in Servers |-> 0 ]
    /\  vLSyncQuorum    = [ serverId \in Servers |-> {} ]
    /\  vUUIDCounter = [ serverId \in Servers |-> 0 ]
    /\  vCrashVector = [ 
            serverId \in Servers |-> [ 
                rr \in Replicas |-> 0
            ]
        ]
    /\  vCrashVectorReps = [ serverId \in Servers |-> {} ]
    /\  vRecoveryReps    = [ serverId \in Servers |-> {} ]



InitCoordState  ==
    /\  vCoordProcessed = [ c \in Coords |-> {}]  
    /\  vCoordClock    = [ c \in Coords  |-> 1 ]
    /\  vCoordTxns   = [ c \in Coords  |-> {} ]

InitConfigManagerState ==
    /\  vCMStatus = [
            replicaId \in Replicas |->StNormal
        ]
    /\  vCMView = [
            replicaId \in Replicas |-> 0
        ]
    /\  vCMGInfo = [  
            replicaId  \in Replicas |->[
                gView   |-> 0,
                gVec    |-> [ shardId \in Shards |->0 ]
            ]
        ]
    /\  vCMPrepareGInfo =[  
            replicaId  \in Replicas |->[
                gView   |-> 0,
                gVec    |-> [ shardId \in Shards |->0 ]
            ]
        ]
    /\  vCMPrepareReps = [
            replicaId \in Replicas |->  {}
        ]  
    /\  vCMProcessed = [
            replicaId \in Replicas |-> {}
        ]
    

\* (* `^\textbf{\large Helpers}^' *)

PickMax(S) == CHOOSE  x \in S: \A y \in S: y <=x

PickMin(S) == CHOOSE  x \in S: \A y \in S: y >=x

Min(a, b) == IF a < b THEN a ELSE b

Max(a, b) == IF a < b THEN b ELSE a

Send(ms) == messages' = messages \cup ms

SeqToSet(s) ==
  { s[i] : i \in DOMAIN s }
      
IsInjective(s) == 
  (*************************************************************************)
  (* TRUE iff the sequence s contains no duplicates where two elements     *)
  (* a, b of s are defined to be duplicates iff a = b.  In other words,    *)
  (* Cardinality(ToSet(s)) = Len(s)                                        *)
  (*                                                                       *)
  (* This definition is overridden by TLC in the Java class SequencesExt.  *)
  (* The operator is overridden by the Java method with the same name.     *)
  (*                                                                       *)
  (* Also see Functions!Injective operator.                                *)
  (*************************************************************************)
  \A i, j \in DOMAIN s: (s[i] = s[j]) => (i = j)

SetToSeq(S) == 
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

Remove(s, e) ==
    (************************************************************************)
    (* The sequence s with e removed or s iff e \notin Range(s)             *)
    (************************************************************************)
    SelectSeq(s, LAMBDA t: t # e)

SetToSortSeq(S, op(_,_)) ==
  (**************************************************************************)
  (* Convert a set to a sorted sequence that contains all the elements of   *)
  (* the set exactly once, and contains no other elements.                  *)
  (* Not defined via CHOOSE like SetToSeq but with an additional conjunct, *)
  (* because this variant works efficiently without a dedicated TLC override. *)
  (**************************************************************************)
  SortSeq(SetToSeq(S), op)



\* `^\textbf{View ID Helpers}^' 

LeaderID(viewId) == ReplicaOrder[ (viewId % Len(ReplicaOrder)) +1]  \* remember <<>> are 1-indexed    

isLeader(replicaId, viewId) == (replicaId = LeaderID(viewId))

PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE)

ViewGreater(gv1, lv1, gv2, lv2) == 
    IF gv1> gv2 THEN TRUE 
    ELSE
        IF  /\  gv1 = gv2 
            /\  lv1 > lv2 
        THEN    TRUE 
        ELSE    FALSE                                



(* `~
\* ASSUME
\*   /\ PrintVal("Three more cats: ",
\*               [cat |-> 1, dog |-> "d"].cat + 3)
\*   /\ PrintVal("Here's a record: ",
\*               [ [game |-> "baseball", player |-> "Marris", homers |-> 61]
\*                    EXCEPT !.player = "McGuire",
\*                           !.homers = @+9 ] )

ASSUME
   /\ PrintVal("isLeader: ", isLeader(1,4))
 ~'
 *)  



(* Coordinator c submits a txn. We assume Coordinator can only send one txn in one tick of time. If time has reached the bound, this client cannot send request any more
*)

LastAppendedTimestamp(Log) == IF Len(Log)=0 THEN 0
                               ELSE Tail(Log).timestamp

CoordSubmitTxn(c)   ==  
    /\ vCoordClock[c] < MaxTime 
    /\ Cardinality(vCoordTxns[c]) < MaxReqNum
    /\  LET
            txnId == [
                coordId |-> c,
                rId     |-> Cardinality(vCoordTxns[c])+1
            ]
        IN                        
        /\  Send({[ mtype   |-> MTxn,
                txnId   |-> txnId,
                command |-> "",
                \* Here we assume involves all shards
                shards  |-> Shards,
                st      |-> vCoordClock[c], 
                bound   |-> LatencyBounds[c],
                sender  |-> c, 
                dest    |-> serverId
            ]: serverId \in Servers })
        /\ vCoordClock' = [ vCoordClock EXCEPT ![c] = vCoordClock[c] + 1 ]
        /\ vCoordTxns' = [ vCoordTxns EXCEPT ![c] = vCoordTxns[c] \cup {txnId} ]


HandleTxn(m) == 
    LET 
        myServerId == m.dest
        newLog == [
            mtype   |-> MLogEntry,
            txnId   |-> m.txnId,
            command |-> m.command,
            shards  |-> m.shards,
            timestamp|-> Max(LastAppendedTimestamp(vLog[myServerId]), m.st + m.bound)
        ]
        serversInOneReplica == {s \in Servers: s.replicaId = myServerId.replicaId} 
    IN
    \/  /\ isLeader(myServerId.replicaId, vLView[myServerId])
        /\ vEarlyBuffer' = [
            vEarlyBuffer EXCEPT ![myServerId]
                = vEarlyBuffer[myServerId] \cup {newLog}]
        \* Broadcast timestamp notifications to other shards
        /\ Send({[
            mtype   |-> MTimestampNotification,
            gView   |-> vGView[myServerId],
            lView   |-> vLView[myServerId],
            sender  |-> myServerId,
            dest    |-> dstServerId,
            entry   |-> newLog
            ]: dstServerId \in serversInOneReplica })
        /\  UNCHANGED  << vLateBuffer >>
    \/  /\  ~isLeader(myServerId.replicaId, vLView[myServerId])
        /\  \/  /\ newLog.timestamp = (m.st + m.bound)
                /\ vEarlyBuffer' = [
                        vEarlyBuffer EXCEPT ![myServerId]
                            = vEarlyBuffer[myServerId] \cup {newLog}
                    ]
                /\  UNCHANGED << vLateBuffer >>
            \/  /\ ~(newLog.timestamp = (m.st + m.bound))
                /\   vLateBuffer' = [
                        vLateBuffer EXCEPT ![myServerId]
                            = vLateBuffer[myServerId] \cup {newLog}
                    ]
                /\  UNCHANGED  << vEarlyBuffer >>
        /\ UNCHANGED  << networkVars >>



HandleTimestampNotification(m) ==    
    LET   
        myServerId == m.dest
        quorum == {
            msg \in vTimestampQuorum[myServerId] 
                :   /\ msg.entry.txnId = m.entry.txnId
                    /\ msg.gView = m.gView
                    /\ m.gView = vGView[myServerId]
            } \cup { m }
    IN
    \* Only leader does timestamp agreement
    /\  vGView[myServerId] = m.gView
    /\  vGVec[myServerId][m.sender.shardId] = m.lView
    /\  isLeader(myServerId.replicaId, vLView[myServerId])
    /\  vTimestampQuorum' = [
            vTimestampQuorum EXCEPT ![myServerId] 
                = vTimestampQuorum[myServerId] \cup {m}
        ]
    /\  IF  Cardinality(quorum) = Cardinality(m.entry.shards)   
        THEN
        (* Timestamp quorum established : Update the timestamp of the txn in Sequencer *)
            LET 
                maxTimestampTxn == 
                    CHOOSE x \in quorum : 
                        \A y \in quorum: 
                            y.entry.timestamp <= x.entry.timestamp 
                sequencingTxn == 
                    CHOOSE x \in vEarlyBuffer[myServerId]: 
                        x.txnId = m.entry.txnId  
            IN
            IF maxTimestampTxn.entry.timestamp > sequencingTxn.timestamp 
            THEN 
                vEarlyBuffer' = [ vEarlyBuffer EXCEPT ![myServerId] 
                    = (vEarlyBuffer[myServerId] \ {sequencingTxn}) \cup {maxTimestampTxn.entry} ]
            ELSE UNCHANGED  << vEarlyBuffer >>
        
        ELSE    
        (* Timestamp quorum not sufficient so far: do not take further actions *)
            UNCHANGED  << vEarlyBuffer >>
        
            

HandleInterReplicaSync(m) ==
    /\ m.lView = vLView[m.dest]
    (* Even if m's crashVector is newer (larger value), we do not accept it.The consistency of crashVector will finally be solved during viewchange 
    *)
    /\ m.crashVector[m.sender] = vCrashVector[m.sender]
    /\ ~isLeader(m.dest.replicaId, vLView[m.dest])
    /\ LET 
        myServerId == m.dest
        syncedTxnIds == { m.entries[i].txnId : i \in 1..Len(m.entries)} 
        currentSyncPoint == Len(vLSyncPoint[myServerId])
        IN
        \/  /\  currentSyncPoint < Len(m.entries)
            /\  vLog' = [vLog EXCEPT ![myServerId] = m.entries]
            (* Kick synced entries out of earlyBuffer 
            *)
            /\  vEarlyBuffer' = [ 
                    vEarlyBuffer EXCEPT ![myServerId] 
                        =  { msg \in vEarlyBuffer[myServerId]: 
                            msg.txnId \notin syncedTxnIds }
                ]
            (* Kick synced entries out of late buffer. In actual implementation, InterReplicaSync only carries log indices, and the entries are fetched from Late Buffer first, if still missing, then it will go to ask leader. Such a design can save much unncessary transmission in practice.
            *)
            /\  vLateBuffer' = [ 
                    vLateBuffer EXCEPT ![myServerId] 
                        =  { msg \in vLateBuffer[myServerId]: 
                            msg.txnId \notin syncedTxnIds }
                ]
            (* Kick synced entries out of timestamp quorum. These txns have been synced, no need to record in TimestampQuorum
            *)
            /\  vTimestampQuorum' = [ 
                    vTimestampQuorum EXCEPT ![myServerId]
                        = { msg \in vTimestampQuorum[myServerId]: 
                            msg.txnId \notin syncedTxnIds}
                ]
            /\  vLSyncPoint' = [
                    vLSyncPoint EXCEPT ![myServerId] = Len(m.entries)] 
            (* Send slow-replies to coordinators
            *)
            /\  Send({[
                    mtype   |-> MSlowReply,
                    sender  |-> myServerId,
                    dest    |-> m.entries[i].txnId.coordId,
                    gView   |-> vGView[myServerId],
                    lView   |-> vLView[myServerId],
                    txnId   |-> m.entries[i].txnId,
                    logId   |-> i
                ]: i \in (currentSyncPoint+1)..Len(m.entries) })
        \/  /\  currentSyncPoint >= Len(m.entries)
            \* Noting new to sync
            /\  UNCHANGED << networkVars, vLog, vEarlyBuffer, 
                            vLateBuffer, vTimestampQuorum, vLSyncPoint>>



StartLeaderFail(serverId) == 
    \*This leader fails
    LET 
        serversInOneShard == {
            s \in Servers: s.shardId = serverId.shardId
        }
        aliveReplicas == { 
            s \in serversInOneShard:    /\  vServerStatus[s] = StNormal
                                        /\  s # serverId  
        }
    IN
    \* if the current alive replicas are less than QuorumSize
    \* Then no more replicas in this sharding group can fail (by assumption of consensus)
    IF Cardinality(aliveReplicas) > QuorumSize THEN
        vServerStatus' = [vServerStatus EXCEPT ![serverId]= StFailing ]
    ELSE    UNCHANGED <<vServerStatus>>


DetectLeaderFail(cmReplicaId) ==
    \E shardId \in Shards:
        LET 
            lView == vCMGInfo[cmReplicaId].gVec[shardId]
            leaderId == LeaderID(lView)
            serverId == [
                replicaId   |-> leaderId,
                shardId     |-> shardId
            ]
        IN
        vServerStatus[serverId] = StFailing

SelectProperLView(currentView, shardId) ==
    LET 
        aliveReplicaId == CHOOSE replicaId \in Replicas: 
                            vServerStatus[shardId][replicaId] = StNormal 
    IN 
        (* Ensure （1） the new view is larger than currentView 
        * (2) its corresponding leader happens to be the selected aliveReplicaId
        *)
        (currentView \div Cardinality(Replicas) +1) * Cardinality(Replicas) + aliveReplicaId

PrepareViewChange(cmReplicaId) == 
    LET 
        newGVec == [
            shardId \in Shards |->
                SelectProperLView(vCMGInfo[cmReplicaId].gVec[shardId], shardId)
        ]
    IN
    /\  vCMPrepareGInfo' = [ vCMPrepareGInfo EXCEPT ![cmReplicaId] = 
            [
                gView   |-> vCMGInfo[cmReplicaId].gView + 1,
                gVec    |->  newGVec
            ]
        ]
    /\  Send({[
            mtype   |-> MCMPrepare,
            sender  |-> cmReplicaId,
            dest    |-> dstRid,
            cView   |-> vCMView[cmReplicaId],
            gView   |-> vCMPrepareGInfo'[cmReplicaId].gView,
            gVec    |->  newGVec

        ]: dstRid \in Replicas })


LaunchViewChange(cmReplicaId) ==
    IF  /\  isLeader(cmReplicaId, vCMView[cmReplicaId]) 
        /\  DetectLeaderFail(cmReplicaId)
    THEN    
        PrepareViewChange(cmReplicaId)
    ELSE 
        UNCHANGED  << networkVars >>




HandleCMPrepare(m) ==
    /\  m.cView = vCMView[m.dest]
    /\  m.gView > vCMGInfo[m.dest].gView
    /\  vCMPrepareGInfo' = [ vCMPrepareGInfo EXCEPT ![m.dest] = 
            [
                gView   |-> m.gView,
                gVec    |->m.gVec
            ]
        ]
    /\  Send({[
            mtype   |-> MCMPrepareReply,
            sender  |-> m.dest,
            dest    |-> m.src,
            cView   |-> m.cView,
            gView   |-> m.gView
        ]})

 
HandleCMPrepareReply(m) ==
    /\  m.cView = vCMView[m.dest]
    /\  isLeader(m.dest, vCMView[m.dest])
    /\  m.gView = vCMPrepareGInfo[m.dest].gView
    /\  vCMPrepareReps' = [vCMPrepareReps EXCEPT ![m.dest] = 
            vCMPrepareReps[m.dest] \cup {m}
        ]
    /\  LET 
            quorum == {mm \in vCMPrepareReps[m.dest]: mm.gView = m.gView}
        IN
        IF Cardinality(quorum) = QuorumSize THEN 
            \* Quorum sufficient, the prepared GInfo is persisted and can be safely used
            /\  vCMGInfo' = [vCMGInfo EXCEPT ![m.dest] = 
                    vCMPrepareGInfo[m.dest]
                ]
            \* notify other follower CM, so that they can catch up with the leader
            /\  Send({[
                    mtype   |-> MCMCommit,
                    sender  |-> m.dest,
                    dest    |-> rid,
                    cView   |-> m.cView,
                    gView   |-> m.gView
                ]: rid \in { r \in Replicas: r # m.dest } })
            \* start view change, broadcast view change request to every server
            /\  Send({[
                    mtype   |-> MViewChangeReq,
                    sender  |-> m.dest,
                    dest    |-> serverId,
                    gView   |-> vCMGInfo'[m.dest].gView,
                    gVec    |-> vCMGInfo'[m.dest].gVec
                ]: serverId \in Servers })
        ELSE 
            UNCHANGED << networkVars, vCMGInfo >>

HandleCMCommit(m) ==
    /\  m.cView = vCMView[m.dest]
    /\  ~isLeader(m.dest, vCMView[m.dest])
    /\  m.gView = vCMPrepareGInfo[m.dest].gView
    /\  vCMGInfo' = [vCMGInfo EXCEPT ![m.dest] = 
                    vCMPrepareGInfo[m.dest]
        ]



HandleViewChangeReq(m) ==    
    LET 
        myServerId == m.dest 
        myLeader == CHOOSE s \in Servers: 
                    /\  s.replicaId = LeaderID(m.gVec[myServerId.shardId])
                    /\  s.shardId = myServerId.shardId
    IN         
    \* If the msg's view is lower, ignore
    /\  vGView[myServerId] < m.gView 
    /\  IF vServerStatus[myServerId] = StNormal THEN
            /\  vServerStatus' = [vServerStatus EXCEPT ![myServerId] =StViewChange]
            /\  vLastNormView' = [vLastNormView EXCEPT ![myServerId] =vLView[myServerId]]
        ELSE    UNCHANGED  << vServerStatus, vLastNormView >>
    /\  vGView' = [
            vGView EXCEPT ![myServerId] = m.vGView
        ]
    /\  vGVec' = [
            vGVec EXCEPT ![myServerId] = m.gVec
        ]
    /\  vLView' = [
            vLView EXCEPT ![myServerId] = m.gVec[myServerId.shardId]
        ]
    \* Clear ealry buffer, 
    /\  vEarlyBuffer' = [
            vEarlyBuffer EXCEPT ![myServerId] = {}
        ]
    \* Clear late buffer 
    /\  vLateBuffer' = [
            vLateBuffer EXCEPT ![myServerId] = {}
        ]
    \* Clear timestamp quorum
    /\  vTimestampQuorum' = [
            vTimestampQuorum EXCEPT ![myServerId] = {}
        ]
    \* Clear vCrossShardVerifyReps
    /\  vCrossShardVerifyReps' = [
            serverId \in Servers |-> {}
        ]
    \* Send ViewChange to the myLeader
    /\  Send({[
                mtype       |-> MViewChange,
                sender      |-> myServerId,
                dest        |-> myLeader,
                gView       |-> m.vGView,
                gVec        |-> m.gVec,
                lView       |-> vLView'[myServerId],
                lastNormal  |-> vLastNormView'[myServerId],
                lSyncPoint  |-> vLSyncPoint[myServerId],
                entries     |-> vLog[myServerId],
                cv          |-> vCrashVector[myServerId]
            ] })

(* Define a comparison function based on the key 
*)
Compare(a, b) ==    
    \/ a.timestamp < b.timestamp
    \/  /\ a.timestamp = b.timestamp 
        /\ a.txnId.coordId < b.txnId.coordId
    \/  /\ a.timestamp = b.timestamp 
        /\ a.txnId.coordId = b.txnId.coordId
        /\ a.txnId.rId < b.txnId.rId


isCrashVectorValid(m) == 
    /\  \A rr \in Replicas: vCrashVector[m.dest][rr]<= m.cv[rr]
    /\  vCrashVector' = [
            vCrashVector EXCEPT ![m.dest] = [
                rr \in Replicas |-> Max(m.cv[rr], vCrashVector[m.dest][rr])
            ]
        ]

CountVotes(entry, logSets) == 
    LET
        validCandidates == { s \in logSets: \E e \in s: 
                                /\ e.timestamp = entry.timestamp 
                                /\ e.txnId = entry.txnId } 
    IN 
        Cardinality(validCandidates)


ReBuildLogs(vcQuorum) == 
    LET 
        refinedQuorum ==  { m \in vcQuorum:
                                \A msg \in vcQuorum: msg.lastNormal <= m.lastNormal } 
        lSyncPoints == {m.lSyncPoint : m \in refinedQuorum }
        largestLSyncPointVC == CHOOSE vc \in refinedQuorum:
                                \A sp \in lSyncPoints: sp <= vc.lSyncPoint 
        syncedLogSeq == SubSeq(largestLSyncPointVC.entries, 1, largestLSyncPointVC.lSyncPoint)
        timestampBoundary == IF largestLSyncPointVC.lSyncPoint =0 THEN 0
                            ELSE syncedLogSeq[largestLSyncPointVC.lSyncPoint].timestamp 
        logSets == { SeqToSet(m.entries): m \in refinedQuorum} 
        allLogs == UNION logSets
        allUnSyncedLogs == { entry \in allLogs: entry.timestamp > timestampBoundary}
        unSyncedLogs == { entry \in allUnSyncedLogs: 
            CountVotes(entry, logSets)>=RecoveryQuorumSize} 
        unSyncedLogSeq == SetToSortSeq(unSyncedLogs, Compare)
    IN
    syncedLogSeq \o unSyncedLogSeq

SelectEntriesBeyondCommitPoint(entries, timestamp) ==
    LET 
        validLogIndices == {
            i \in 1..Len(entries): entries[i].timestamp> timestamp
        }
        startIndex == PickMin(validLogIndices)
    IN
    SubSeq(entries, startIndex, Len(entries))

HandleViewChange(m) ==
    LET 
        myServerId == m.dest 
        serversInOneShard == { s \in Servers: s.shardId = myServerId.shardId }
        leadersInAllShard == { 
                s \in Servers: s.replicaId = isLeader(s.replicaId, m.gVec[s.shardId]) 
        }
    IN
    /\  \/  ViewGreater(m.gView, m.lView, vGView[myServerId], vLView[myServerId]) 
        \/  /\  m.gView = vGView[myServerId]
            /\  m.lView = vLView[myServerId]
            /\  vServerStatus[myServerId] = StViewChange
    /\  isLeader(myServerId.replicaId, m.lView)
    /\  vGView' = [vGView EXCEPT ![myServerId] = m.gView]
    /\  vLView' = [vLView EXCEPT ![myServerId] = m.lView]
    /\  vGVec' = [vGVec EXCEPT ![myServerId] = m.gVec]
    /\  vViewChange' = [
            vViewChange EXCEPT ![myServerId] = {
                vc \in vViewChange[myServerId]:
                    vc.lView = m.lView
            } \cup { m }
        ]
    /\  IF Cardinality(vViewChange'[myServerId]) = QuorumSize THEN 
            /\  vLog' = [ vLog EXCEPT ![myServerId] = ReBuildLogs(vViewChange'[myServerId])]
            /\  vServerStatus' = [vServerStatus EXCEPT ![myServerId] = StCrossShardSyncing]
            (* Even after the log is recovered within one shard,
                * The newly elected leader cannot StartView
                * It needs to verify with other shards' leaders to ensure strict serializability
                *)
            /\  vViewChange' = [vViewChange EXCEPT ![myServerId] = {}]
            /\  Send({[
                    mtype      |-> MCrossShardVerifyReq,
                    sender     |-> myServerId,
                    dest       |-> dst,
                    lView      |-> vLView'[myServerId],
                    gView      |-> vGView'[myServerId],
                    syncedDdl  |-> vLog[myServerId][vLSyncPoint[myServerId]].timestamp
                ] : dst \in leadersInAllShard} )
        ELSE 
            /\  vServerStatus' = [vServerStatus EXCEPT ![myServerId] = StViewChange ] 
            /\  UNCHANGED << networkVars, vLog>>

HandleCrossShardVerifyReq(m) ==
    LET 
        myServerId == m.dest 
        myLog == vLog[myServerId]
        logSet == SeqToSet(myLog)
        unVerifiedLogs == { 
            e \in logSet:   /\  e.timestamp > m.syncedDdl 
                            /\  m.sender \in e.shards 
        }
        unVerifiedLogList == SetToSortSeq(unVerifiedLogs, Compare)
    IN
    /\  m.gView = vGView[myServerId]
    /\  m.lView = vGVec[myServerId][m.sender.shardId]
    /\  Send({[
            mtype      |-> MCrossShardVerifyRep,
            sender     |-> myServerId,
            dest       |-> m.sender,
            lView      |-> vLView[myServerId],
            gView      |-> vGView[myServerId],
            entries    |-> unVerifiedLogList
        ]})

HandleCrossShardVerifyRep(m) ==
    LET
        myServerId == m.dest 
        myLog == vLog[myServerId]
        myLogSet == SeqToSet(myLog)
    IN 
    /\  m.gView = vGView[myServerId]
    /\  m.lView = vGVec[myServerId][m.sender.shardId] 
    /\  vCrossShardVerifyReps' = [
            vCrossShardVerifyReps EXCEPT ![myServerId]= 
                vCrossShardVerifyReps[myServerId] \cup {m} ]
    /\  IF Cardinality(vCrossShardVerifyReps'[myServerId]) = Cardinality(Shards) 
        THEN
            LET 
                unVerifiedLogs == UNION { SeqToSet(mm.entries) : 
                    mm \in vCrossShardVerifyReps'[myServerId] }
                maxTimestampLogs == {
                    e \in unVerifiedLogs:
                        \A x \in unVerifiedLogs: 
                            \/ x.txnId # e.txnId 
                            \/ x.timestamp <= e.timestamp
                }
                agreedLogs == { 
                    e \in maxTimestampLogs :
                        \* the reciving shard is missing this txn
                        \/  \A x \in myLogSet: x.txnId # e.txnId 
                        \/  \E x \in myLogSet: x.timestamp < e.timestamp 
                }
                goodLogs == {
                    e \in myLogSet : \A x \in agreedLogs: x.txnId # e.txnId
                }
                completeLogs == goodLogs \cup agreedLogs 
                newLogList == SetToSortSeq(completeLogs, Compare)
            IN 
                vLog' = [vLog EXCEPT ![myServerId] = newLogList]
        ELSE 
            UNCHANGED << vLog >>                
                



BuildGlobalConsistentLog(serverId, entries) == 
    LET
        myEntries == {
            entry \in entries : /\ serverId \in entry.shards 
                                /\ \A e \in entries:
                                    IF e.txnId = entry.txnId THEN 
                                        e.timestamp <= entry.timestamp 
                                    ELSE TRUE
        }
    IN 
    SetToSortSeq(myEntries, Compare)


HandleStartView(m) ==
    LET 
        myServerId == m.dest 
    IN
    /\  \/  ViewGreater(m.gView, m.lView, vGView[myServerId], vLView[myServerId])
        \/  /\  m.gView = vGView[myServerId]
            /\  m.lView = vLView[myServerId]
            /\  \/  vServerStatus[myServerId] = StViewChange
                \/  vServerStatus[myServerId] = StRecovering
    /\  vGView' = [ vGView EXCEPT ![myServerId]= m.gView ]
    /\  vLView' = [ vLView EXCEPT ![myServerId] = m.gLView ]
    /\  vGVec' = [ vGVec EXCEPT ![myServerId] = m.vGVec ]
    /\  vServerStatus' = [ vServerStatus EXCEPT ![myServerId] = StNormal]
    /\  vLog' = [vLog EXCEPT ![myServerId] = m.entries]
    /\  vEarlyBuffer' = [ vEarlyBuffer EXCEPT ![myServerId] = {} ]
    /\  vLateBuffer' = [ vLateBuffer EXCEPT ![myServerId] = {} ]
    /\  vTimestampQuorum' = [ vTimestampQuorum EXCEPT ![myServerId] = {} ]
    /\  vCrossShardVerifyReps' = [
            vCrossShardVerifyReps EXCEPT ![myServerId] = {}
        ]
    /\  vLSyncPoint' = [vLSyncPoint EXCEPT ![myServerId] = Len(vLog'[myServerId])]
    /\  vLastNormView' = [vLastNormView EXCEPT ![myServerId] = m.lView]
    /\  vViewChange' = [ vViewChange EXCEPT ![myServerId] = {}]
    /\  vLSyncQuorum' = [ vLSyncQuorum EXCEPT ![myServerId] = {} ]
    /\  vCrashVectorReps' = [ vCrashVectorReps EXCEPT ![myServerId] = {}]
    /\  vRecoveryReps' = [ vRecoveryReps EXCEPT ![myServerId] = {}]


ResetServerState(serverId) ==
    /\  vLog' = [vLog EXCEPT ![serverId] = <<>>]
    /\  vEarlyBuffer' = [ vEarlyBuffer EXCEPT ![serverId] = {}]
    /\  vLateBuffer' = [vLateBuffer EXCEPT ![serverId] = {}]
    /\  vTimestampQuorum' = [vTimestampQuorum EXCEPT ![serverId] = {}]
    /\  vCrossShardVerifyReps' = [ 
            vCrossShardVerifyReps EXCEPT ![serverId] = {} 
        ]
    /\  vGView' = [vGView EXCEPT ![serverId] = 0]
    /\  vGVec' = [ vGVec EXCEPT ![serverId] = [ s \in Shards |-> 0] ]
    /\  vLView' = [ vLView EXCEPT ![serverId] = 0]
    /\  vLastNormView' = [vLastNormView EXCEPT ![serverId] = 0]
    /\  vViewChange' =[vViewChange EXCEPT ![serverId] = {}]
    /\  vLSyncPoint' = [ vLSyncPoint EXCEPT ![serverId] = 0 ]
    /\  vLCommitPoint' = [ vLCommitPoint EXCEPT ![serverId] = 0 ]
    /\  vLSyncQuorum' = [ vLSyncQuorum EXCEPT ![serverId] = {} ]
    /\  vCrashVector' = [vCrashVector EXCEPT ![serverId] = [
            rr \in Replicas |->0
        ]]
    /\  vCrashVectorReps' = [ vCrashVectorReps EXCEPT ![serverId] = {}]
    /\  vRecoveryReps' = [ vRecoveryReps EXCEPT ![serverId] = {} ]
    /\  vServerProcessed' = [ vServerProcessed EXCEPT ![serverId] = {} ]

StartServerRecovery(serverId) ==
    LET
        serversInOneShard == {
            s \in Servers: s.shardId = serverId.shardId
        }
        nonce ==  vUUIDCounter[serverId]+1
    IN 
    /\  vServerStatus' = [vServerStatus EXCEPT ![serverId] = StRecovering]
    /\  vUUIDCounter' = [ vUUIDCounter EXCEPT ![serverId] = vUUIDCounter[serverId]+1]
    /\  Send({[
            mtype       |-> MCrashVectorReq,
            sender      |-> serverId, 
            dest        |-> dst,
            nonce       |-> nonce
        ]: dst \in serversInOneShard})

HandleCrashVectorReq(m) ==
    LET 
        myServerId == m.dest
    IN 
    /\  vServerStatus[myServerId] = StNormal
    /\  Send({[
            mtype       |-> MCrashVectorRep,
            sender      |-> myServerId, 
            dest        |-> m.sender,
            nonce       |-> m.nonce,
            cv          |-> vCrashVector[myServerId]
        ]})


AggregateCV(serverId) ==
    LET 
        cvQuorum == { m.cv: m \in vCrashVectorReps[serverId] }
        cvValQuorum == [ rr \in Replicas |-> { cv[rr]: cv \in cvQuorum }  ]
    IN 
        [ rr \in Replicas |-> PickMax(cvValQuorum[rr])]

HandleCrashVectorRep(m) ==
    LET 
        myServerId == m.dest 
        serversInOneShard == { s \in Servers: s.shardId = myServerId.shardId }
    IN 
    /\  vServerStatus[myServerId] = StRecovering
    /\  vUUIDCounter[myServerId] = m.nonce 
    /\  vCrashVectorReps' = [
            vCrashVectorReps EXCEPT ![myServerId] = vCrashVectorReps \cup {m}
        ]
    /\  IF Cardinality(vCrashVectorReps'[myServerId]) = QuorumSize THEN 
            LET 
                acv == AggregateCV(myServerId)
                myCV == [ acv EXCEPT ![myServerId] = acv[myServerId]+1 ]
            IN
            /\  vCrashVector' = [
                    vCrashVector EXCEPT ![myServerId] = myCV
                ]
            /\  Send({[
                    mtype         |-> MRecoveryReq,
                    sender        |-> myServerId,
                    dest          |-> dst,
                    cv            |-> myCV
                ]: dst \in serversInOneShard})
        ELSE    UNCHANGED << networkVars, vCrashVector>>




HandleRecoveryReq(m)==
    LET 
        myServerId == m.dest 
    IN 
    /\  vServerStatus[myServerId] = StNormal
    /\  Send({[
            mtype   |-> MRecoveryRep,
            sender  |-> myServerId,
            dest    |-> m.sender,
            gView   |-> vGView[myServerId],
            lView   |-> vLView[myServerId],
            cv      |-> vCrashVector'[myServerId]
        ]})


HandleRecoveryRep(m) ==
    LET 
        myServerId == m.dest 
    IN 
    /\  vServerStatus[myServerId] = StRecovering
    /\  vRecoveryReps' = [
            vRecoveryReps EXCEPT ![myServerId] 
                = vRecoveryReps[myServerId] \cup {m}
        ]
    /\  IF Cardinality(vRecoveryReps[myServerId]) = QuorumSize THEN 
            LET 
                lViewQuorum == { mm.lView : mm \in vRecoveryReps[myServerId]}
                gViewQuorum == { mm.gView : mm \in vRecoveryReps[myServerId]}
            IN
            /\  vLView' = [ vLView EXCEPT ![myServerId] = PickMax(lViewQuorum) ]
            /\  vGView' = [ vLView EXCEPT ![myServerId] = PickMax(gViewQuorum) ]
            /\  Send({[
                    mtype       |-> MStartViewReq,
                    sender      |-> myServerId,
                    dest        |-> [
                                        replicaId |-> LeaderID(vLView[myServerId]),
                                        shardId   |-> myServerId.shardId 
                                    ],
                    lView       |-> vLView'[myServerId],
                    cv          |-> vCrashVector'[myServerId]
                ]})
        ELSE UNCHANGED  <<networkVars, vLView, vGView>> 



HandleStartViewReq(m) ==
    LET 
        myServerId == m.dest 
    IN
    /\  vServerStatus[myServerId] = StNormal
    /\  vLView[myServerId] = m.lView 
    /\  isLeader(myServerId.replicaId, vLView[myServerId])
    /\  Send({[
            mtype      |-> MStartView,
            sender     |-> myServerId,
            dest       |-> m.sender,
            lView      |-> vLView[myServerId],
            gView      |-> vGView[myServerId],
            gVec       |-> vGVec[myServerId],
            entries    |-> vLog[myServerId],
            cv         |-> vCrashVector[myServerId]
        ]})



StartLocalSync(serverId) ==
    LET 
        leaderServerId == [
            replicaId |-> LeaderID(vLView[serverId]),
            shardId   |-> serverId.shardId
        ]
    IN 
    /\  vServerStatus[serverId] = StNormal
    /\  Send({[
            mtype       |-> MLocalSyncStatus,
            sender      |-> serverId,
            dest        |-> leaderServerId,
            lView       |-> vLView[serverId],
            lSyncPoint  |-> vLSyncPoint[serverId],
            cv          |-> vCrashVector[serverId]
        ]})


HandleLocalSyncStatus(m) ==
    LET 
        myServerId == m.dest 
        lSyncQuorum == vLSyncQuorum[myServerId]
    IN 
    /\  vServerStatus[myServerId] = StNormal
    /\  vLView[myServerId] = m.lView 
    /\  isLeader(myServerId.replicaId, vLView[myServerId])
    /\  \A mm \in lSyncQuorum: 
        \/  mm.sender # m.sender 
        \/  mm.lSyncPoint < m.lSyncPoint 
    /\  vLSyncQuorum' = [
            vLSyncQuorum EXCEPT ![myServerId] = 
                { mm \in lSyncQuorum: mm.sender # m.sender } \cup {m}
        ]
    /\  IF Cardinality(vLSyncQuorum'[myServerId]) >= QuorumSize THEN 
            LET 
                candidateQuorum == {
                    R \in SUBSET(vLSyncQuorum'[myServerId]):   
                        Cardinality(R) = QuorumSize
                }
                quorumSyncPoints == {
                    {x.lSyncPoint : x \in R}: R \in candidateQuorum
                }
                validCommitPoints == {PickMax(Q): Q \in quorumSyncPoints }
                maxCommitPoint == PickMax(validCommitPoints)
            IN 
            /\  vLCommitPoint' = [vLCommitPoint EXCEPT ![myServerId] = maxCommitPoint]
            /\  Send({[
                    mtype       |-> MLocalCommit,
                    sender      |-> myServerId,
                    dest        |-> m.sender,
                    lView       |-> vLView[myServerId],
                    lCommitPoint|-> vLCommitPoint'[myServerId],
                    cv          |-> vCrashVector'[myServerId]
                ]})
        ELSE    UNCHANGED << vLCommitPoint, networkVars >>
                    


HandleLocalCommit(m) ==
    LET 
        myServerId == m.dest 
    IN 
    /\  vServerStatus[myServerId] = StNormal
    /\  vLView[myServerId] = m.lView 
    /\  ~isLeader(myServerId.replicaId, vLView[myServerId])
    \* Make sure the syncPoint is large enough before updating CommitPoint
    /\  IF  /\  vLSyncPoint[myServerId] >= m.lCommitPoint  
            /\  vLCommitPoint[myServerId] < m.lCommitPoint
        THEN 
            vLCommitPoint' = [
                vLCommitPoint EXCEPT ![myServerId] = m.lCommitPoint
            ]
        ELSE UNCHANGED << vLCommitPoint >>




isCommitting(txn, timestampQ) == 
    LET quorum == { msg \in timestampQ: msg.entry.txnId =txn.txnId}
    IN  Cardinality(quorum) = Cardinality(txn.shards)
                                

ReleaseSequencer(serverId, currentTime) == 
    LET
        serversInOneShard == { s \in Servers: s.shardId = serverId.shardId }
        expireTxns == 
            { msg \in vEarlyBuffer[serverId]:
                /\ msg.timestamp <= currentTime }
        sortedTxnList == SetToSortSeq(expireTxns, Compare)
        committingStatus == 
            [ i \in 1..Len(sortedTxnList) 
                |-> isCommitting(sortedTxnList[i], vTimestampQuorum[serverId])
            ]
        canReleaseTxnIndices == {
            i \in 1..Len(sortedTxnList):
                \A j \in 1..i: committingStatus[j] = TRUE } 
        \* Here we consider all txns are not commutative, 
        \* Therefore,  At most one txn can be speculatively executed with risk 
        \* Refer to Section 3.6 of Tiga paper
        specTxnIndex == {
            i \in 1..Len(sortedTxnList):
                /\  \A j \in 1..(i-1): committingStatus[j] = TRUE 
                /\  committingStatus[i] = FALSE 
        }  
               
    IN
    IF  Cardinality(canReleaseTxnIndices) =0  \* Nothing to release
    THEN    
        /\  UNCHANGED  <<vLog, vEarlyBuffer, vLateBuffer, vTimestampQuorum >>  
        \* While there is nothing to release, some txns might be speculatively executed (Section 3.6 of Tiga paper)   
        /\  IF Cardinality(specTxnIndex) > 0 THEN 
                Send({[
                    mtype   |-> MFastReply,
                    sender  |-> serverId,
                    dest    |-> sortedTxnList[i].txnId.coordId,
                    gView   |-> vGView[serverId],
                    lView   |-> vLView[serverId],
                    txnId   |-> sortedTxnList[i].txnId,
                    hash    |-> [
                                log |-> vLog'[serverId],
                                cv  |-> vCrashVector
                                ],
                    t       |-> sortedTxnList[i].timestamp,
                    logId   |-> 0 \* logId=0 indicates this is a speculative txn with rollback risk, 
                                  \* we need to compare the timestamps from different shards to decide 
                                  \* whether the execution results are serializable
                ]: i \in specTxnIndex })        
            ELSE
                UNCHANGED <<networkVars>>
    ELSE 
        LET  
            releaseUpTo == CHOOSE i \in canReleaseTxnIndices: 
                            \A j \in canReleaseTxnIndices : j <=i 
            releaseSeq == SubSeq(sortedTxnList, 1, releaseUpTo)
            releaseTxns ==  {releaseSeq[i]: i \in 1..Len(releaseSeq)}
        IN
        /\ vEarlyBuffer' =[
            vEarlyBuffer EXCEPT ![serverId] 
                = vEarlyBuffer[serverId] \ releaseTxns ]
        /\ vTimestampQuorum' = [
            vTimestampQuorum EXCEPT ![serverId]
                = { msg \in vTimestampQuorum[serverId]: 
                    \A txn \in releaseTxns: txn.txnId # msg.entry.txnId}
            ]
        \* Append to log
        /\ vLog' = [vLog EXCEPT ![serverId] = vLog[serverId] \o releaseSeq ]
        /\  IF isLeader(serverId.replicaId, vLView[serverId]) THEN
                /\ vLSyncPoint' = [vLSyncPoint EXCEPT  ![serverId] = Len(vLog'[serverId])]
            ELSE    UNCHANGED << vLSyncPoint >>
        \* Send fast-replies to coordinators
        /\ Send({[
            mtype   |-> MFastReply,
            sender  |-> serverId,
            dest    |-> sortedTxnList[i].txnId.coordId,
            gView   |-> vGView[serverId],
            lView   |-> vLView[serverId],
            txnId   |-> sortedTxnList[i].txnId,
            hash    |-> [
                        log |-> vLog'[serverId],
                        cv  |-> vCrashVector
                    ],
            t       |->0, \* timestamp=0 indicates this is not a speculative txn with rollback risk
            logId   |-> i
            ]: i \in (1+Len(vLog[serverId]))..Len(vLog'[serverId]) })
        \* Send InterReplicaSync to the other servers in the same sharding group
        \* In real implementation, we send the log indices incrementally (i.e., consider it as an optimization)
        \* Here for clarity and simplicity, we always send the whole log list
        /\ Send({[
                mtype   |-> MInterReplicaSync,
                lView   |-> vLView[serverId],
                sender  |-> serverId,
                dest    |-> dstServerId,
                entries |-> vLog'[serverId]
            ]: dstServerId \in serversInOneShard })
        /\  IF Cardinality(specTxnIndex) > 0 THEN 
                Send({[
                    mtype   |-> MFastReply,
                    sender  |-> serverId,
                    dest    |-> sortedTxnList[i].txnId.coordId,
                    gView   |-> vGView[serverId],
                    lView   |-> vLView[serverId],
                    txnId   |-> sortedTxnList[i].txnId,
                    hash    |-> [
                                log |-> vLog'[serverId],
                                cv  |-> vCrashVector
                                ],
                    t       |-> sortedTxnList[i].timestamp,
                    logId   |-> 0 \* logId=0 indicates this is a speculative txn with rollback risk
                ]: i \in specTxnIndex })        
            ELSE
                TRUE



ServerClockMove(serverId) == 
    IF  vServerClock[serverId] >= MaxTime   THEN 
        UNCHANGED  <<networkVars, serverStateVars>>
    ELSE 
        /\  vServerClock' = [ 
                vServerClock EXCEPT ![serverId] = vServerClock[serverId] +1]
        /\  IF  vServerStatus[serverId] = StNormal THEN
                /\  ReleaseSequencer(serverId, vServerClock[serverId] +1)
            ELSE    
                UNCHANGED <<networkVars, vLog, vEarlyBuffer, 
                    vLateBuffer, vTimestampQuorum>>
        /\  UNCHANGED << vCrossShardVerifyReps,
                vServerStatus, vGView, vGVec, vLView, vLastNormView,
                vViewChange, vLSyncPoint, vLCommitPoint, 
                vLSyncQuorum,vUUIDCounter, vCrashVector, 
                vCrashVectorReps,vRecoveryReps, vServerProcessed >>


CoordClockMove(coordId) ==  
    \/  /\ vCoordClock[coordId] >= MaxTime
        /\ UNCHANGED  << vCoordClock >>
    \/  /\ vCoordClock[coordId] < MaxTime
        /\ vCoordClock' = [ 
            vCoordClock EXCEPT ![coordId] = vCoordClock[coordId] +1]

Init == 
    /\ InitNetworkState
    /\ InitServerState
    /\ InitCoordState
    /\ InitConfigManagerState
    /\ ActionName = <<"Init">>


Next == 
    \/  /\ ActionName' = <<"Next">>
        /\ UNCHANGED << networkVars, serverStateVars, 
                        coordStateVars, configManagerStateVars>>
    \/  \E c \in Coords:
        /\ Cardinality(vCoordTxns[c]) < MaxReqNum
        /\ CoordSubmitTxn(c)
        /\ UNCHANGED <<serverStateVars, configManagerStateVars, 
                    vCoordProcessed>>
        /\ ActionName' = <<"CoordSubmitTxn">>

    \/ \E m \in messages:
        /\ m.mtype = MTxn
        /\ vServerStatus[m.dest] = StNormal
        /\ m \notin vServerProcessed[m.dest]
        /\ vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
            vServerProcessed[m.dest] \cup {m} ]
        /\ HandleTxn(m)
        /\ UNCHANGED  << coordStateVars, configManagerStateVars,
            vLog,vTimestampQuorum, vCrossShardVerifyReps, 
            vServerStatus, vGView, vGVec,
            vLView, vServerClock, vLastNormView, 
            vViewChange, vLSyncPoint, vLCommitPoint,  
            vLSyncQuorum, vUUIDCounter, vCrashVector, 
            vCrashVectorReps, vRecoveryReps>>
        /\ ActionName' = <<"HandleTxn">>

    \/ \E m \in messages:
        /\ m.mtype = MTimestampNotification
        /\ vServerStatus[m.dest] = StNormal
        /\ m \notin vServerProcessed[m.dest]
        /\ vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
            vServerProcessed[m.dest] \cup {m} ]
        /\ HandleTimestampNotification(m)
        /\ UNCHANGED  << networkVars, coordStateVars, configManagerStateVars, 
                vLog, vCrossShardVerifyReps, vLateBuffer, vServerStatus, 
                vGView, vGVec, vLView, vServerClock, vLastNormView, 
                vViewChange, vLSyncPoint, vLCommitPoint, vLSyncQuorum, 
                vUUIDCounter, vCrashVector, vCrashVectorReps, vRecoveryReps>>
        /\ ActionName' = <<"HandleTimestampNotification">>

    \/ \E m \in messages:
        /\ m.mtype = MInterReplicaSync
        /\ vServerStatus[m.dest] = StNormal
        /\ m \notin vServerProcessed[m.dest]
        /\ vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
            vServerProcessed[m.dest] \cup {m} ]
        /\ HandleInterReplicaSync(m)
        /\ UNCHANGED << coordStateVars, configManagerStateVars,
                vLog,  vCrossShardVerifyReps, vLateBuffer, 
                vServerStatus, vGView, vGVec, vLView, 
                vServerClock, vLastNormView, 
                vViewChange, vLCommitPoint, 
                vLSyncQuorum, vUUIDCounter, vCrashVector, 
                vCrashVectorReps, vRecoveryReps>>                    
        /\ ActionName' = <<"HandleInterReplicaSync">>


    \* Some Leader(s) fail 
    \/ \E serverId \in Servers: 
        /\ vLView[serverId] < MaxViews
        /\ isLeader(serverId.replicaId, vLView[serverId])
        /\ vServerStatus[serverId] = StNormal
        /\ StartLeaderFail(serverId)
        /\ UNCHANGED << networkVars, coordStateVars, configManagerStateVars, 
            vLog, vEarlyBuffer, vLateBuffer, vTimestampQuorum, 
            vCrossShardVerifyReps, vGView, vGVec, vLView, vServerClock, 
            vLastNormView, vViewChange, vLSyncPoint, vLCommitPoint, 
            vLSyncQuorum, vUUIDCounter, vCrashVector, vCrashVectorReps, 
            vRecoveryReps, vServerProcessed>>
        /\ ActionName' = << "StartLeaderFail" >>

    \* Config Manager notices some leader(s) fail and launch view change
    \/  \E cmReplicaId \in Replicas:
        /\  LaunchViewChange(cmReplicaId)
        /\  UNCHANGED  << coordStateVars, serverStateVars, configManagerStateVars >>
        /\  ActionName' = << "LaunchViewChange" >>

    \/  \E m \in messages:
        /\  m.mtype = MCMPrepare
        /\  m \notin vCMProcessed[m.dest]
        /\  vCMProcessed' = [vCMProcessed EXCEPT ![m.dest] = 
                vCMProcessed[m.dest] \cup {m}]
        /\  vCMStatus[m.dest] = StNormal 
        /\  HandleCMPrepare(m)
        /\  UNCHANGED  <<coordStateVars, serverStateVars >>
        /\ ActionName' = << "HandleCMPrepare" >>


    \/  \E m \in messages:
        /\  m.mtype = MCMPrepareReply
        /\  m \notin vCMProcessed[m.dest]
        /\  vCMProcessed' = [vCMProcessed EXCEPT ![m.dest] = 
                vCMProcessed[m.dest] \cup {m}]
        /\  vCMStatus[m.dest] = StNormal 
        /\  HandleCMPrepareReply(m)
        /\  UNCHANGED  <<coordStateVars, serverStateVars, 
                        vCMStatus, vCMView, vCMPrepareGInfo >>
        /\ ActionName' = << "HandleCMPrepareReply" >>

    \/  \E m \in messages:
        /\  m.mtype = MCMCommit
        /\  m \notin vCMProcessed[m.dest]
        /\  vCMProcessed' = [vCMProcessed EXCEPT ![m.dest] = 
                vCMProcessed[m.dest] \cup {m}]
        /\  vCMStatus[m.dest] = StNormal 
        /\  HandleCMCommit(m)
        /\  UNCHANGED  <<networkVars, coordStateVars, serverStateVars, 
                        vCMStatus, vCMView, vCMPrepareGInfo, vCMPrepareReps>>
        /\ ActionName' = << "HandleCMCommit" >>


    \/  \E m \in messages:
        /\  m.mtype = MViewChangeReq
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  \/  vServerStatus[m.dest] = StNormal 
            \/  vServerStatus[m.dest] = StViewChange 
        /\  HandleViewChangeReq(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vLog, vServerClock, vViewChange, vLSyncPoint, 
                vLCommitPoint, vLSyncQuorum, vUUIDCounter, 
                vCrashVector, vCrashVectorReps, vRecoveryReps >>
        /\ ActionName' = << "HandleViewChangeReq" >>


    \/  \E m \in messages:
        /\  m.mtype = MViewChange
        /\  isCrashVectorValid(m)
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  \/  vServerStatus[m.dest] = StNormal 
            \/  vServerStatus[m.dest] = StViewChange 
        /\  HandleViewChange(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vGVec, vServerClock, vLSyncPoint, vLastNormView,
                vLCommitPoint, vLSyncQuorum, vUUIDCounter, 
                vCrashVector, vCrashVectorReps, vRecoveryReps >>
        /\ ActionName' = << "HandleViewChange" >>

    \/  \E m \in messages:
        /\  m.mtype = MCrossShardVerifyReq
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StCrossShardSyncing
        /\  HandleCrossShardVerifyReq(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vLog, vEarlyBuffer, vLateBuffer, vTimestampQuorum, 
                vCrossShardVerifyReps, vServerStatus, 
                vGView, vGVec, vLView, vServerClock, vLastNormView, 
                vViewChange, vLSyncPoint, vLCommitPoint, vLSyncQuorum,
                vUUIDCounter, vCrashVector, vCrashVectorReps, 
                vRecoveryReps>>
        /\ ActionName' = << "HandleCrossShardVerifyReq" >>


    \/  \E m \in messages:
        /\  m.mtype = MCrossShardVerifyRep
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StCrossShardSyncing
        /\  HandleCrossShardVerifyRep(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vEarlyBuffer, vLateBuffer, vTimestampQuorum, vServerStatus, 
                vGView, vGVec, vLView, vServerClock, vLastNormView, 
                vViewChange, vLSyncPoint, vLCommitPoint, 
                vLSyncQuorum, vUUIDCounter, vCrashVector, 
                vCrashVectorReps, vRecoveryReps>>
        /\ ActionName' = << "HandleCrossShardVerifyRep" >>

    \/  \E m \in messages:
        /\  m.mtype = MStartView
        /\  isCrashVectorValid(m)
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] # StFailing
        /\  HandleStartView(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                    vServerClock,vLCommitPoint, 
                    vUUIDCounter, vCrashVector >>
        /\ ActionName' = << "HandleStartView" >>

    \* Failed server rejoin                    
    \/ \E serverId \in Servers: 
        /\ vServerStatus[serverId] = StFailing
        /\ vServerStatus' = [vServerStatus EXCEPT ![serverId] = StRecovering ]
        /\ ResetServerState(serverId)
        /\ StartServerRecovery(serverId)
        /\ UNCHANGED << networkVars, coordStateVars, configManagerStateVars>>
        /\ ActionName' = << "StartReplicaRecovery">>

    \/  \E m \in messages:
        /\  m.mtype = MCrashVectorReq
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StNormal
        /\  HandleCrashVectorReq(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vLog, vEarlyBuffer, vLateBuffer, vTimestampQuorum, 
                vCrossShardVerifyReps, vServerStatus, vGView, vGVec,
                vLView, vServerClock, vLastNormView, vViewChange, 
                vLSyncPoint, vLCommitPoint, vLSyncQuorum, vUUIDCounter, 
                vCrashVector, vCrashVectorReps, vRecoveryReps >>
        /\ ActionName' = << "HandleCrashVectorReq" >>

    \/  \E m \in messages:
        /\  m.mtype = MCrashVectorRep
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StRecovering
        /\  HandleCrashVectorRep(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vLog, vEarlyBuffer, vLateBuffer, 
                vTimestampQuorum, vCrossShardVerifyReps, vServerStatus, 
                vGView, vGVec, vLView, vServerClock, vLastNormView, 
                vViewChange, vLSyncPoint, vLCommitPoint,vLSyncQuorum,
                vUUIDCounter, vCrashVectorReps, vRecoveryReps >>
        /\ ActionName' = << "HandleCrashVectorRep" >>

    \/  \E m \in messages:
        /\  m.mtype = MRecoveryReq
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StNormal
        /\  isCrashVectorValid(m)
        /\  HandleRecoveryReq(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vLog, vEarlyBuffer, vLateBuffer, 
                vTimestampQuorum, vCrossShardVerifyReps, vServerStatus, 
                vGView, vGVec, vLView, vServerClock, vLastNormView, 
                vViewChange, vLSyncPoint, vLCommitPoint, vLSyncQuorum,
                vUUIDCounter, vCrashVectorReps, vRecoveryReps >>
        /\ ActionName' = << "HandleRecoveryReq" >>

    \/  \E m \in messages:
        /\  m.mtype = MRecoveryRep
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StRecovering
        /\  isCrashVectorValid(m)
        /\  HandleRecoveryRep(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vLog, vEarlyBuffer, vLateBuffer, 
                vTimestampQuorum, vCrossShardVerifyReps, vServerStatus, 
                vGVec, vServerClock, vLastNormView, vViewChange, 
                vLSyncPoint, vLCommitPoint, vLSyncQuorum,
                vUUIDCounter, vCrashVectorReps, vRecoveryReps >>
        /\ ActionName' = << "HandleRecoveryRep" >>

    \/  \E m \in messages:
        /\  m.mtype = MStartViewReq
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StCrossShardSyncing
        /\  isCrashVectorValid(m)
        /\  HandleStartViewReq(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vLog, vEarlyBuffer, vLateBuffer, vTimestampQuorum, 
                vCrossShardVerifyReps, vServerStatus, 
                vGView, vGVec, vLView, vServerClock, 
                vLastNormView, vViewChange, vLSyncPoint, 
                vLCommitPoint, vLSyncQuorum,
                vUUIDCounter, vCrashVector, 
                vCrashVectorReps, vRecoveryReps >>
        /\ ActionName' = << "HandleStartViewReq" >>

    \* Periodic Sync
    \/  \E serverId \in Servers:
        /\  vServerStatus[serverId] = StNormal
        /\  StartLocalSync(serverId) 
        /\  UNCHANGED  << coordStateVars, 
                serverStateVars, configManagerStateVars>>
        /\  ActionName' = << "StartLocalSync" >>

    \/  \E m \in messages:
        /\  m.mtype = MLocalSyncStatus
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StNormal
        /\  isCrashVectorValid(m)
        /\  HandleLocalSyncStatus(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                vLog, vEarlyBuffer, vLateBuffer, vTimestampQuorum, 
                vCrossShardVerifyReps, vServerClock, vViewChange, 
                vGVec, vGView, vLSyncPoint, vLView, vLastNormView,
                vServerStatus,vUUIDCounter, vCrashVectorReps, 
                vRecoveryReps >>
        /\ ActionName' = << "HandleLocalSyncStatus" >>


    \/  \E m \in messages:
        /\  m.mtype = MLocalCommit
        /\  m \notin vServerProcessed[m.dest]
        /\  vServerProcessed' =[vServerProcessed EXCEPT ![m.dest]=
                vServerProcessed[m.dest] \cup {m} ]
        /\  vServerStatus[m.dest] = StNormal
        /\  isCrashVectorValid(m)
        /\  HandleLocalCommit(m)
        /\  UNCHANGED  << coordStateVars, configManagerStateVars,
                networkVars, vLog, vEarlyBuffer, vLateBuffer, 
                vTimestampQuorum, vCrossShardVerifyReps, 
                vServerStatus, vServerClock, vGView, vGVec, 
                vLView, vLastNormView, vViewChange, vLSyncPoint, 
                vLSyncQuorum, vUUIDCounter, vCrashVectorReps, vRecoveryReps >>
        /\ ActionName' = << "HandleLocalCommit" >>


    \* Clock Move
    \/ \E serverId \in Servers: 
        /\ ServerClockMove(serverId)                             
        /\ UNCHANGED << coordStateVars, configManagerStateVars >>
        /\ ActionName' = << "ServerClockMove">>

    \/ \E coordId \in Coords:
        /\ CoordClockMove(coordId)
        /\ UNCHANGED << networkVars, serverStateVars, configManagerStateVars,
            vCoordTxns, vCoordProcessed >>
        /\ ActionName' = << "CoordClockMove">>

Spec == Init /\ [][Next]_<<networkVars,serverStateVars, coordStateVars, 
                        configManagerStateVars,ActionName>>


ShardRecovered(shardId, lViewID) ==  
    LET 
        serversInOneShard == { s \in Servers: s.shardId = shardId }
        leaderServer == [
            replicaId |-> LeaderID(lViewID),
            shardId |-> shardId
        ]
    IN
    /\ \E RM \in SUBSET(serversInOneShard): 
        /\  Cardinality(RM) >= QuorumSize
        /\  leaderServer \in RM 
        /\  \A  r \in RM: vServerStatus[r] = StNormal 
        /\  \A  r \in RM: vLastNormView[r] >= lViewID



CommittedInView(v, shardId, txnId) == 
    LET 
        serversInOneShard == { s \in Servers: s.shardId = shardId }
        leaderServer == [
            replicaId |-> LeaderID(v),
            shardId |-> shardId
        ]
        replySet == {
            m \in messages: /\  \/  m.mtype = MFastReply
                                \/  m.mtype = MSlowReply
                            /\  m.txnId = txnId 
                            /\  m.sender \in serversInOneShard
                            /\  m.lView = v
        }
    IN
    IF \A reply \in replySet: 
        \/  reply.mtype # MFastReply
        \/  reply.sender # leaderServer 
    THEN \* No leader's fast reply-> This txn is not committed
        FALSE 
    ELSE
        LET 
            leaderReply == CHOOSE reply \in replySet: 
                                /\  reply.mtype = MFastReply
                                /\  reply.sender = leaderServer
        IN
        \* Committed in Fast Path
        \/  \E fastQuorum \in SUBSET replySet:
                /\  leaderReply \in fastQuorum
                /\  Cardinality(fastQuorum) = FastQuorumSize
                \*  All replies have the same hash (or it is a slow reply)
                /\  \A reply \in fastQuorum:
                        \/  /\  reply.mtype = MFastReply 
                            /\  reply.hash = leaderReply.hash 
                        \* Slow Reply can be used as fast reply
                        \/  reply.mtype = MSlowReply  
        \* Committed in Slow Path
        \/  \E slowQuorum \in SUBSET  replySet:
                /\  leaderReply \in slowQuorum
                /\  Cardinality(slowQuorum) = QuorumSize
                /\  \A reply \in slowQuorum \ {leaderReply}:
                        reply.mtype = MSlowReply


(* `^\textbf{\large Invariants }^' *)
(*
Durability [In-Shard-Property]: Committed txns always survive failure
i.e. If a txn is committed (to be more precise, locally committed) in one view,  then it will remain committed in the higher views.

One thing to note, the check of "committed" only happens when the system is still "normal". While the system is under recovery (i.e. less than f+1 replicas are normal), the check of committed does not make sense
*)
Durability == 
    \A shardId \in Shards:
        \A v1, v2 \in 0..MaxViews:
            \* If a txn is committed in lower view (v1,), 
            \* it is impossible to make this request uncommited in higher vie
            ~(  /\  v1 < v2
                /\  ShardRecovered(shardId, v2)
                /\  \E c \in Coords:
                        \E txnId \in vCoordTxns[c]:
                            /\  CommittedInView(v1, shardId, txnId)
                            /\  ~CommittedInView(v2, shardId, txnId)
            )


(*
Consistency [In-Shard-Property]: Committed txns have the same history even after view changes, i.e. If a request is committed in a lower view (v1), then (based on Durability Property), then it remains committed in higher view (v2)

Consistency requires the history of the txns (i.e. all the txs before this txn) remain the same   
*)

Consistency ==
    \A shardId \in Shards:
        \A v1, v2 \in 1..MaxViews:   
            ~(  /\ v1 < v2
                \* To check Consistency of txns in higher views, 
                \* the shard should have entered the higher views
                /\ ShardRecovered(shardId, v2) 
                /\ \E c \in Coords :
                    \E txnId \in vCoordTxns[c]:
                        \* Durability has been checked in another invariant
                        IF  /\ CommittedInView(v1, shardId, txnId)
                            /\ CommittedInView(v2, shardId, txnId)
                        THEN  
                            LET 
                                v1LeaderReply == CHOOSE m \in messages: 
                                                    /\  m.mtype = MFastReply
                                                    /\  m.txnId = txnId
                                                    /\  m.lView = v1
                                                    /\  m.sender.shardId = shardId 
                                                    /\  m.sender.replicaId = LeaderID(v1) 
                                v2LeaderReply == CHOOSE m \in messages: 
                                                    /\  m.mtype = MFastReply
                                                    /\  m.txnId = txnId
                                                    /\  m.lView = v2
                                                    /\  m.sender.shardId = shardId 
                                                    /\  m.sender.replicaId = LeaderID(v2)                                                                 
                            IN
                                v1LeaderReply.hash # v2LeaderReply.hash 
                        ELSE FALSE
            )

(*
Linearizability [In-Shard-Property]: Only one txn can be committed for a given position, i.e. If one txn has committed at position i, then no contrary observation can be made

i.e. there cannot be a second txn committed at the same position
*)

Linearizability == 
    LET 
        allTxns == UNION { vCoordTxns[c]: c \in Coords }
    IN
    \A shardId \in Shards:
        \A txnId1, txnId2 \in allTxns:
            IF txnId1 = txnId2 THEN TRUE 
            ELSE 
                \A v1, v2 \in 1..MaxViews:
                    IF  /\  CommittedInView(v1, shardId, txnId1)
                        /\  CommittedInView(v1, shardId, txnId2)
                    THEN 
                        LET 
                            v1LeaderReply == CHOOSE m \in messages: 
                                                /\  m.mtype = MFastReply
                                                /\  m.txnId = txnId1
                                                /\  m.lView = v1
                                                /\  m.sender.shardId = shardId 
                                                /\  m.sender.replicaId = LeaderID(v1) 
                            v2LeaderReply == CHOOSE m \in messages: 
                                                /\  m.mtype = MFastReply
                                                /\  m.txnId = txnId2
                                                /\  m.lView = v2
                                                /\  m.sender.shardId = shardId 
                                                /\  m.sender.replicaId = LeaderID(v2)                                                                 
                        IN
                            \* They cannot be committed in the same log position, regardless of the view
                            v1LeaderReply.logId # v2LeaderReply.logId
                    ELSE \* Not both are committed, so no need to check
                        TRUE


(*
Serializability [Cross-Shard-Property]: Given two txns and two shards: If they are both committed in both shards, then they should be committed in the same order, i.e., if txn-1 committed before txn-2 on Shard-1, then txn-1 is also committed before txn-2 on Shard-2
*)

Serializability == 
    LET 
        allTxns == UNION { vCoordTxns[c]: c \in Coords }
    IN
    \A txnId1, txnId2 \in allTxns:
        IF txnId1 = txnId2 THEN TRUE 
        ELSE 
            \A v \in 1..MaxViews:
                \A shardId1, shardId2 \in Shards:
                    IF shardId1 = shardId2 THEN TRUE 
                    ELSE 
                        IF  /\  CommittedInView(v, shardId1, txnId1)
                            /\  CommittedInView(v, shardId1, txnId2)
                            /\  CommittedInView(v, shardId2, txnId1)
                            /\  CommittedInView(v, shardId2, txnId2)
                        THEN 
                            LET 
                                txn1_LeaderReplyOnShard1 == CHOOSE m \in messages: 
                                                    /\  m.mtype = MFastReply
                                                    /\  m.txnId = txnId1
                                                    /\  m.lView = v
                                                    /\  m.sender.shardId = shardId1 
                                                    /\  m.sender.replicaId = LeaderID(v) 
                                txn2_LeaderReplyOnShard1 == CHOOSE m \in messages: 
                                                    /\  m.mtype = MFastReply
                                                    /\  m.txnId = txnId2
                                                    /\  m.lView = v
                                                    /\  m.sender.shardId = shardId1 
                                                    /\  m.sender.replicaId = LeaderID(v)    
                                txn1_LeaderReplyOnShard2 == CHOOSE m \in messages: 
                                                    /\  m.mtype = MFastReply
                                                    /\  m.txnId = txnId1
                                                    /\  m.lView = v
                                                    /\  m.sender.shardId = shardId2 
                                                    /\  m.sender.replicaId = LeaderID(v) 
                                txn2_LeaderReplyOnShard2 == CHOOSE m \in messages: 
                                                    /\  m.mtype = MFastReply
                                                    /\  m.txnId = txnId2
                                                    /\  m.lView = v
                                                    /\  m.sender.shardId = shardId2 
                                                    /\  m.sender.replicaId = LeaderID(v)                                                              
                            IN
                            IF  /\  txn1_LeaderReplyOnShard1.t = txn1_LeaderReplyOnShard2.t 
                                /\  txn2_LeaderReplyOnShard1.t = txn2_LeaderReplyOnShard2.t 
                            THEN
                                \/  /\  txn1_LeaderReplyOnShard1.logId > txn2_LeaderReplyOnShard1.logId 
                                    /\  txn1_LeaderReplyOnShard2.logId > txn2_LeaderReplyOnShard2.logId
                                \/  /\  txn1_LeaderReplyOnShard1.logId < txn2_LeaderReplyOnShard1.logId 
                                    /\  txn1_LeaderReplyOnShard2.logId < txn2_LeaderReplyOnShard2.logId
                            ELSE
                                \* if their timestamps are not equal, our coordinator will not consider them as committed, 
                                \* We do not need to check such cases 
                                TRUE                                 
                        ELSE TRUE
================================================================================
