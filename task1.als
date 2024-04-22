sig Principal {}

sig Data {}

sig Message {
	seq_num : one Int,
	src : one Principal,
	dest : one Principal,
	data : one Data
}

abstract sig ChannelState {}
one sig Insecure , Secure extends ChannelState {}

abstract sig DebugAction {}
one sig SendAction , RecvAction , AttackerAction , GoSecureAction
	extends DebugAction {}

one sig State {
	// send_counter [ from ][ to] records the number of messages that Principal
	// ’from ’ has sent to Principal ’to ’
	var send_counter : Principal -> Principal -> one Int ,
	// recv_counter [to ][ from ] records the number of messages that Principal
	// ’to ’ has received from principal ’from ’
	var recv_counter : Principal -> Principal -> one Int ,
	var channel_state : one ChannelState ,
	// the network can hold at most one message at a time
	var network : lone Message ,
	// for debugging purposes (to aid reading counter - examples , etc .)
	// records the most recent action that has occurred
	var debug_last_action : lone DebugAction
}

// sender ’from ’ sends a message to receiver ’to ’ with sequence number
// ’seqnum ’ and data ’d’
pred Send [from , to : Principal , seqnum : Int , d : Data ] {
	no State . network
	( some m : Message |
	 m.src = from 
	and m. dest = to 
	and m. seq_num = seqnum
	and seqnum = State.send_counter [from ,to] 
	and m. data = d
	and m in State.network')
	State.send_counter' = State . send_counter ++ ( from -> to -> (add[seqnum ,1]))
	State.recv_counter' = State . recv_counter
	State.channel_state' = State . channel_state
	State.debug_last_action' = SendAction
}

//Task 1.1 Recv predicate
// receiver ’to ’ receives a message from sender ’from ’ with sequence number
// ’seqnum ’ and data ’d’
pred Recv [from , to : Principal , seqnum : Int , d : Data ] {
	one State.network and no State.network'
	(some m:Message | 
	m.src = from 
	and m.dest = to 
	and m.seq_num = seqnum
	and seqnum = State.recv_counter[to, from] 
	and m.data = d
	and m in State.network)
	State.recv_counter' = State.recv_counter ++ (to -> from -> (add[seqnum, 1]))
	State.send_counter' = State.send_counter
	State.channel_state' = State.channel_state
	State.debug_last_action' = RecvAction
}

// models the establishment of a secure channel
pred Go_Secure {
	no State . network

	State . channel_state = Insecure and State . channel_state' = Secure

	State . send_counter' = State . send_counter
	State . recv_counter' = State . recv_counter
	State . network' = State.network
	State . debug_last_action' = GoSecureAction
}

pred Attacker_Action {
	(one State.network and one State.network' and State.channel_state = Insecure and
	some m1, m2 : Message | m1 != m2 and m1 in State.network and m2 in State.network')
	or
	(one State.network and no State.network')
	or
	(no State.network and one State.network' and State.channel_state = Insecure)
	State.send_counter' = State.send_counter
	State.recv_counter' = State.recv_counter
	State.channel_state' = State.channel_state
	State.debug_last_action' = AttackerAction
}

// the initial state
pred Init {
	State . send_counter = Principal -> Principal -> 0
	State . recv_counter = Principal -> Principal -> 0
	State . channel_state = Insecure
	no State . network
	no State . debug_last_action
}

pred State_Transition {
	( some from , to : Principal , seqnum : Int , d : Data |
	Send [from ,to , seqnum ,d] or Recv [from ,to , seqnum ,d])
	or
	Go_Secure
	or
	Do_Nothing
	or
	Attacker_Action
}

pred Do_Nothing {
	State . send_counter' = State . send_counter
	State . recv_counter' = State . recv_counter
	State . network' = State . network
	State . channel_state' = State . channel_state
	no State . debug_last_action'
}

pred Send_Recv_Test[] {
    some a: Principal, b: Principal, seqnum: Int, d: Data | 
    {
        Send[a, b, seqnum, d]
	and after
        Recv[a, b, seqnum, d]
    }
}

// 想得到Recv的instance,需要执行
run Send_Recv_Test

// constrain traces
fact traces {
	Init and
	( always State_Transition )
}

// Task 1.2 assertion in_sync_always
assert in_sync_always{
	always all p,q : Principal | 
	State.send_counter[p,q] = State.recv_counter [q,p]
	and
	State.send_counter[q,p] = State.recv_counter[p,q]
}

check in_sync_always for 2 

assert in_sync {
	always all p, q:Principal, seqnum : Int , d : Data | State.channel_state = Secure and
	Recv[p,q,seqnum,d] implies after (State.send_counter[p,q] = State.recv_counter[q ,p])
}

check in_sync for 2

pred Once_Send[from,to:Principal, seqnum:Int,d:Data] {
	once (State.channel_state = Secure and Send[from,to,seqnum,d])
}

pred Once_Recv[from,to:Principal, seqnum:Int,d:Data] {
	once (State.channel_state = Secure and Recv[from,to,seqnum,d])
}

assert security_goal {
	always all p: Principal, q: Principal, seqnum1,seqnum2: Int, d: Data |
		State.channel_state = Secure and Recv[p,q,seqnum2,d]
		=> Once_Send[p,q,seqnum2,d]
		=> Once_Send[p,q,seqnum1,d]
		=> Once_Recv[p,q,seqnum1,d]
}

check security_goal for 2 but 4..14 steps
