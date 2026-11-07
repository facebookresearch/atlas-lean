# Exact comparison count of naive matching

Let $p = p_0 \cdots p_{m-1}$ be a pattern and
$t = t_0 \cdots t_{n-1}$ a text. If $m \le n$, the number of symbol comparisons performed by the
naive matcher on $p$ and $t$ is

$$\sum_{s=0}^{n-m} \min(m, k_s + 1),$$

where $k_s$ is the least $i < m$ such that $p_i$ and $t_{s+i}$ are unequal under the Boolean
equality of the alphabet, and $k_s = m$ if there is no such $i$. If $m > n$, the naive matcher
performs no comparisons.
