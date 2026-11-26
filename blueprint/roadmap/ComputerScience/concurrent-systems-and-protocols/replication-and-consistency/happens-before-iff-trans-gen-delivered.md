# Happened-before between updates, by delivery

Read a well-formed execution, one in which
every receipt names an earlier position, as an execution of a replicated system whose replicas
are the processes: an event that receives no message issues a new update, identified with the
position of that event, and an event that receives from position $i$ delivers the update issued
at position $i$. Suppose that every receipt names a position that holds an issue. Say that an
update $a$ precedes an update $b$ directly when the replica that issues $b$ has issued or
delivered $a$ before it issues $b$: some position $k < b$ holds an event of that replica that
either is the issue of $a$ ($k = a$) or delivers $a$. Then for any two updates $u_1$ and $u_2$,
position $u_1$ happened before position $u_2$ in Lamport's sense if and only if there is a chain
$u_1 = v_0, v_1, \dots, v_m = u_2$ of updates with $m \ge 1$ in which each $v_l$ precedes
$v_{l+1}$ directly. So happened-before between updates is the transitive closure of the
replica-local order of issues and of the order from delivering an update to issuing a later one
at the same replica.
