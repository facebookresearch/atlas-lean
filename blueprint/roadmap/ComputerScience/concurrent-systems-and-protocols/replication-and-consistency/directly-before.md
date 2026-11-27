# An update directly precedes another, by delivery

Read an execution $e_0, \dots, e_{n-1}$,
whose events each belong to a process and may receive the message of the event at some position,
as an execution of a replicated system whose replicas are the processes: an event that receives no
message issues a new update, identified with the position of that event, and an event that
receives from position $i$ delivers the update issued at position $i$. An update $a$ directly
precedes an update $b$ when the replica that issues $b$ has issued or delivered $a$ before it
issues $b$: positions $a$ and $b$ hold issues, and some position $k < b$ holds an event of the
replica that issues $b$ that either is the issue of $a$ ($k = a$) or delivers $a$. This is the
relation by which Shapiro et al. define happened-before between updates: $a$ belongs to the
causal history of the replica of $b$ just before $b$ is issued.
