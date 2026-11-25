# Sulanke array B

The Sulanke array $B$ assigns a natural number $B(k, i)$ to every pair of
natural numbers $k$ and $i$. It is defined by recursion on $k$: $B(0, 0) = 1$, $B(0, i) = 0$ for
$i \ge 1$, $B(k+1, 0) = B(k, 0)$, and for all $k$ and $i$

$$B(k+1, i+1) = \bigl(B(k, i+1) + 2B(k, i)\bigr) + \bigl(B(k, i) + 2B(k, i-1)\bigr),$$

where $B(k, -1)$ is read as $0$.

This is the recurrence obtained by eliminating the Sulanke array $A$, given by
$A(k+1, i) = B(k, i) + 2B(k, i-1)$, from $B(k+1, i) = A(k+1, i) + A(k+1, i-1)$, with values at
negative indices read as $0$.
