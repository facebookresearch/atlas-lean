# Digit reversal

For natural numbers $b$ and $n$ with $b \ge 2$, write
$n = \sum_{i\lt k} d_i b^i$ with digits $0 \le d_i < b$ and leading digit $d_{k-1} \ne 0$ (so $k = 0$
when $n = 0$). The base-$b$ reversal of $n$ is the natural number $\sum_{i\lt k} d_{k-1-i} b^i$. For
the bases $b = 0$ and $b = 1$ the reversal of $n$ is $n$ itself.

Trailing zeros of $n$ become leading zeros and are lost: in base $10$ the reversal of $120$ is
$21$.
