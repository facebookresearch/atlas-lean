# Randomized MTS is $O(\log^2 n)$-competitive on every metric

On every $n$-point metric space there is a randomized online algorithm for metrical task systems that is $O(\log^2 n)$-competitive against oblivious adversaries.

## Proof sketch

Bubeck, Cohen, J. R. Lee and Y. T. Lee run continuous-time mirror descent on the polytope of probability measures over the leaves of a weighted tree, with a regularizer that sums entropies of the conditional distributions at internal nodes weighted by edge lengths; on HSTs this is $O(\text{depth} \cdot \log n)$-competitive. An *unfair gluing* step combines solutions on subtrees of very different sizes so that the overhead depends on $\log n$ rather than on the depth, giving $O(\log n)$ on suitable trees, and the remaining $O(\log n)$ factor comes from the tree embedding.

## Depends on

- [Metrical task systems](metrical-task-system.md)

## Proof depends on

- [Competitive ratios transfer through dominating tree embeddings](embedding-transfer.md)
- [Hierarchically separated trees](hierarchically-separated-tree.md)
- [Continuous-time mirror descent for online covering](../randomized-k-server-by-mirror-descent/continuous-mirror-descent-dynamics.md)
- [Fakcharoenphol-Rao-Talwar O(log n) expected-stretch tree embeddings](../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/johnson-lindenstrauss-optimality-and-metric-embeddings/frt-logarithmic-stretch-tree-embedding.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, James R. Lee, Yin Tat Lee, "Metrical Task Systems on Trees via Mirror Descent and Unfair Gluing", SIAM Journal on Computing 50(3) (2021); SODA (2019), arXiv:1807.04404.
