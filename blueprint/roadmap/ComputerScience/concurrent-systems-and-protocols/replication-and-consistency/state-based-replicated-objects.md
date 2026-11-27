# State-based replicated objects

A state-based replicated object has a set $S$ of states and a distinguished initial state $s^0 \in S$. A query call, including its arguments, has a result type and takes a state to a result and a post-state. An update call maps the state of a single replica to a new state. A merge, invoked on receipt of another replica's state, takes the local and received states to a new local state.

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011; INRIA research report RR-7687, Section 2.1
