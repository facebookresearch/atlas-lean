# Causal delivery of updates

Read an execution of the [Lamport clocks](../lamport-clocks/README.md) model, a finite list of events $e_0, \dots, e_{n-1}$ in which each event belongs to a process and may receive the message of the event at some position, as an execution of a replicated system whose replicas are the processes. An event that receives no message issues a new update, identified with the position of that event, and an event that receives from position $i$ delivers the update issued at position $i$. An update $u_1$ happened before an update $u_2$ when the issue of $u_1$ [happened before](../lamport-clocks/happens-before.md) the issue of $u_2$ in Lamport's sense: a chain of events leads from the issue of $u_1$ to the issue of $u_2$, in which each event is followed by a later event that belongs to the same replica or receives from it.

The execution provides *causal delivery* if every replica delivers an update $u_2$ only after it has delivered every update $u_1$ that happened before $u_2$, where a replica counts the updates it issues as delivered. That is, whenever the event at position $j$, of replica $r$, delivers the update $u_2$ issued at position $i_2$, and the update $u_1$ issued at position $i_1$ happened before $u_2$, some position $k < j$ holds an event of $r$ that either issues $u_1$ ($k = i_1$) or delivers it.

Shapiro et al. define happened-before between updates by delivery: $u_1$ happened before $u_2$ when $u_1$ has been delivered at the replica where $u_2$ originates by the time $u_2$ is issued there. When every receipt names an earlier issue, the transitive closure of this order, in which a replica's own earlier updates count as delivered, is the relation above ([Happened-before between updates, by delivery](happens-before-iff-trans-gen-delivered.md)).

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011, 386–400; INRIA research report RR-7687, version 2, 2011, Section 2.4: Definition 2.5 and the definition of happened-before that follows it (p. 7), and the assumption of a reliable causally-ordered broadcast (pp. 7–8)
- L. Lamport, "Time, clocks, and the ordering of events in a distributed system", *Communications of the ACM* 21(7):558–565, 1978, "The Partial Ordering" (definition of happened-before, p. 559)
