# Lamport timestamps increase along each process

Let $e_0, \dots, e_{n-1}$ be an
execution and let $t_k$ be the Lamport timestamp of $e_k$. If $i < j < n$ and $e_i$ and $e_j$
belong to the same process, then $t_i < t_j$.

This is Lamport's clock condition C1, which his implementation rule IR1 guarantees.
