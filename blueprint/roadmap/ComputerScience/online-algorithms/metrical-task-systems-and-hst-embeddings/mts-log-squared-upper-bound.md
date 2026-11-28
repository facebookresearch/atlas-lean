# Randomized MTS is $O(\log^2 n)$-competitive on every metric

On every $n$-point metric space there is a randomized online algorithm for metrical task systems that is $O(\log^2 n)$-competitive against oblivious adversaries.

## Proof sketch

Bubeck, Cohen, J. R. Lee and Y. T. Lee run continuous-time mirror descent on the polytope of probability measures over the leaves of a weighted tree, with a multiscale entropy regularizer that weights the entropies of the conditional distributions at internal nodes by edge lengths; on an $n$-point tree metric of combinatorial depth $D$ this is $O(D \log n)$-competitive. For HSTs, mirror descent refines the standard approach of gluing *unfair* metrical task systems on subtrees, which removes the dependence on the depth and gives an $O(\log n)$-competitive algorithm; the remaining $O(\log n)$ factor comes from embedding an arbitrary $n$-point metric into HSTs with $O(\log n)$ expected distortion.

## Depends on

- [Metrical task systems](metrical-task-system.md)

## Proof depends on

- [Competitive ratios transfer through dominating tree embeddings](embedding-transfer.md)
- [Hierarchically separated trees](hierarchically-separated-tree.md)
- [Continuous-time mirror descent for online covering](../randomized-k-server-by-mirror-descent/continuous-mirror-descent-dynamics.md)
- [Fakcharoenphol-Rao-Talwar O(log n) expected-stretch tree embeddings](../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/johnson-lindenstrauss-optimality-and-metric-embeddings/frt-logarithmic-stretch-tree-embedding.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, James R. Lee, Yin Tat Lee, "Metrical Task Systems on Trees via Mirror Descent and Unfair Gluing", SIAM Journal on Computing 50(3) (2021); SODA (2019), arXiv:1807.04404, Theorem 1.1 and abstract.
