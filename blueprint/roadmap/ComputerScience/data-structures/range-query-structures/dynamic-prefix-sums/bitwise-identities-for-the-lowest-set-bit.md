# Bitwise identities for the lowest set bit

For every natural number $m \ge 1$, with $\mathrm{lowbit}(m)$ the largest power of two dividing $m$ and $\wedge$ bitwise and,

$$
m \wedge (m - 1) = m - \mathrm{lowbit}(m), \qquad m - \left(m \wedge (m - 1)\right) = \mathrm{lowbit}(m).
$$

Both are computable with every intermediate value at most $m$, so they need no word-width mask.

## Proof sketch

Write $m = 2^j (2r + 1)$. Then $m - 1 = 2^{j+1} r + (2^j - 1)$, so $m$ and $m - 1$ agree above bit $j$, and below and at bit $j$ the word $m$ has exactly bit $j$ set while $m-1$ has bits $0, \dots, j-1$ set; their conjunction is $2^{j+1} r = m - 2^j$.

## Depends on

- [Lowest set bit](../fenwick-tree/lowbit.md)

## Sources

- P. M. Fenwick, "A New Data Structure for Cumulative Frequency Tables", Software: Practice and Experience 24(3), pp. 327-336, 1994.
