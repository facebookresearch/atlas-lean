# One round of the scan on a list

Given a list $y_0, \dots, y_{n-1}$ in a monoid $M$ and a
natural number $k$, one round produces the list of length $n$ whose entry $i$ is
$y_{i - 2^k} \, y_i$ when $2^k \le i$ and $y_i$ when $i < 2^k$.

The list is traversed in lockstep with its own suffix starting at position $2^k$, so a round
costs $O(n)$.
