# Size of Batcher's odd-even merge sort

For every $k \in \mathbb{N}$, the number $L$ of
comparators of Batcher's odd-even merge sort on $2^k$ wires satisfies
$4(L + 1) + k \cdot 2^k = (k^2 + 4) \cdot 2^k$, that is, $L = (k^2 - k + 4) \cdot 2^k / 4 - 1$.

The identity is stated without subtraction or division, and is exact for every $k$.
