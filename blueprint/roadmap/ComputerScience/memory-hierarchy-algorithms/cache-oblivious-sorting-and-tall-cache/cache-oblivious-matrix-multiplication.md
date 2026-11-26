# Cache-oblivious matrix multiplication

Under the tall-cache assumption $Z = \Omega(L^2)$, the cache-oblivious algorithm that multiplies an $m \times n$ by an $n \times p$ matrix by recursively halving the largest of the three dimensions incurs $O\!\left(m + n + p + \frac{mn + np + mp}{L} + \frac{mnp}{L\sqrt{Z}}\right)$ cache misses. For square $n \times n$ matrices this is $O\!\left(n^2/L + n^3/(L\sqrt{Z})\right)$ when $n^2 \ge Z$, matching the Hong–Kung lower bound for classical matrix multiplication.

## Proof sketch

Once the three submatrices of a recursive subproblem fit in cache together, which happens when all dimensions are $O(\sqrt{Z})$, the subproblem costs only the misses needed to load its inputs, $O(1 + \cdot/L)$ by the tall-cache assumption applied to row segments. The recursion reaches such subproblems after splitting into $O(mnp/Z^{3/2})$ pieces, each costing $O(Z/L)$, which gives the dominant term. The Hong–Kung red-blue pebble argument shows that any classical algorithm moves $\Omega(n^3/\sqrt{Z})$ words.

## Depends on

- [Cache-oblivious scanning and matrix transposition](../cache-oblivious-algorithms/cache-oblivious-scanning-and-matrix.md)
- [Tall-cache assumptions](tall-cache-assumption.md)
- [Communication lower bound for classical matrix multiplication](../../algebraic-and-numerical-algorithms/communication-lower-bounds/matmul-card-div-sub-le-words.md)

## Proof depends on

- [Cache-oblivious scanning and matrix transposition](../cache-oblivious-algorithms/cache-oblivious-scanning-and-matrix.md)
- [Tall-cache assumptions](tall-cache-assumption.md)
- [Communication lower bound for classical matrix multiplication](../../algebraic-and-numerical-algorithms/communication-lower-bounds/matmul-card-div-sub-le-words.md)

## Sources

- Matteo Frigo, Charles E. Leiserson, Harald Prokop, Sridhar Ramachandran, "Cache-Oblivious Algorithms", FOCS (1999); ACM Transactions on Algorithms 8(1) (2012).
- Jia-Wei Hong, H. T. Kung, "I/O Complexity: The Red-Blue Pebble Game", STOC (1981).
