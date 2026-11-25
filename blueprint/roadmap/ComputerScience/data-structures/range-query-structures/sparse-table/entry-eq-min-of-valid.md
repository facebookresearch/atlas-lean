# Entries of a valid sparse table are interval minima

Let $t$ be a valid sparse table
over a linearly ordered type, with data $d = (d_0, \dots, d_{n-1})$, and let $k$ and $i$ be
natural numbers with $i + 2^k \le n$. Then the entry of $t$ at row $k$ and index $i$ is
defined and equals $\min(d_i, d_{i+1}, \dots, d_{i+2^k-1})$.
