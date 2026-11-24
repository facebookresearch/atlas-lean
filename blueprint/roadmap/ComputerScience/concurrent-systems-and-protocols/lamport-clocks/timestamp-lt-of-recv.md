# A receipt is stamped later than its send

Let $e_0, \dots, e_{n-1}$ be a well-formed
execution and let $t_k$ be the Lamport timestamp of $e_k$. If $j < n$ and $e_j$ receives the
message sent by the event at position $i$, then $t_i < t_j$.

This is Lamport's clock condition C2, which his implementation rule IR2 guarantees.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Logical Clocks", condition C2 and rule IR2, p. 560.
