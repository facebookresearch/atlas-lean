# Entries of a built sparse table are interval minima

Let $a = (a_0, \dots, a_{n-1})$ be
a list over a linearly ordered type, and let $k$ and $i$ be natural numbers with
$i + 2^k \le n$. Then the entry of the sparse table built from $a$ at row $k$ and index $i$ is
defined and equals $\min(a_i, a_{i+1}, \dots, a_{i+2^k-1})$.

No separate bound on $k$ is needed: $i + 2^k \le n$ already implies
$k \le \lfloor \log_2 n \rfloor$.
