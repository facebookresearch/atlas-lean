# A timestamp depends only on a prefix containing its event

Let $e_0, \dots, e_{n-1}$ be
an execution and let $i < k \le n$. The Lamport timestamp of $e_i$ in the whole execution equals
its Lamport timestamp in the prefix $e_0, \dots, e_{k-1}$.
