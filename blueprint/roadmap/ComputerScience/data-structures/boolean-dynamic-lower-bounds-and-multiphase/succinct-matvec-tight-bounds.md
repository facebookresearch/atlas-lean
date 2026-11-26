# Tight cell-probe bounds for succinct Boolean matrix-vector multiplication

There is a succinct structure for Boolean matrix-vector multiplication that stores $\tilde{O}(n^{3/2})$ extra bits and answers queries in $\tilde{O}(n^{3/2})$ probes. Conversely, every structure storing $r$ extra bits with $n < r < n^2$ has query time $t$ satisfying $t \cdot r = \tilde{\Omega}(n^3)$, and every structure with $r \le n$ has $t = \tilde{\Omega}(n^2)$. These bounds carry over to word-RAM structures.

## Proof sketch

For the upper bound, precompute products of $M$ with a random family of vectors so that every query vector differs from a stored combination on few coordinates, which are then handled by reading $\tilde{O}(n^{1/2})$ columns. For the lower bound, pick $M$ uniformly at random; if $tr = o(n^3)$, a cell-sampling argument over the read-only matrix shows that for a random query most probes are into matrix cells that carry information unrelated to the answer, and an encoding of $M$ using the extra bits and the answers to many queries would compress a uniformly random matrix.

## Depends on

- [Succinct Boolean matrix-vector multiplication](succinct-boolean-matvec-problem.md)

## Proof depends on

- [Cell-sampling lemma](../cell-sampling-and-range-counting-lower-bounds/cell-sampling-lemma.md)

## Sources

- Diptarka Chakraborty, Lior Kamma, Kasper Green Larsen, "Tight Cell Probe Bounds for Succinct Boolean Matrix-Vector Multiplication", STOC (2018), arXiv:1711.04467.
