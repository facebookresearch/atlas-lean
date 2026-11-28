# An update directly precedes another, by delivery

Read an execution $e_0, \dots, e_{n-1}$,
whose events each belong to a process and may receive the message of the event at some position,
as an execution of a replicated system whose replicas are the processes: an event that receives no
message issues a new update, identified with the position of that event, and a receipt naming
position $i$ delivers the update at $i$ if that position holds an issue; otherwise it delivers no
update. An update $a$ directly precedes an update $b$ when the replica that issues $b$ has issued
or delivered $a$ before it issues $b$: positions $a$ and $b$ hold issues, and some position
$k < b$ holds an event of the replica that issues $b$ that either is the issue of $a$ ($k = a$) or
delivers $a$. This is the relation by which M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski
define happened-before between updates (*Conflict-free replicated data types*, INRIA research
report RR-7687, version 2, Section 2.4, p. 7: Definition 2.5 and the definition of happened-before
after it): $a$ belongs to the causal history of the replica of $b$ just before $b$ is issued.
