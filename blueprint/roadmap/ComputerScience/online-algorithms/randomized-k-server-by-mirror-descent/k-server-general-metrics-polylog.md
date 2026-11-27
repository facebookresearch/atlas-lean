# Polylogarithmic randomized k-server on general metrics

On every $n$-point metric space there is a randomized online $k$-server algorithm that is $O(\log^2 k \cdot \log n)$-competitive, and on every metric space whose aspect ratio (largest over smallest nonzero distance) is at most $\Delta$ there is one that is $O(\log^3 k \cdot \log \Delta)$-competitive. Earlier, Bansal, Buchbinder, Mądry and Naor gave the first polylogarithmic bound $O(\log^3 n \log^2 k)$.

## Proof sketch

The first bound combines the HST algorithm with the static embedding of $n$-point metrics into HSTs with $O(\log n)$ expected distortion. The second uses a dynamic HST embedding that is constructed online on the requested points only, so that its distortion depends on $\log\Delta$ and the number of relevant scales rather than on $n$, at the price of an extra $\log k$ factor.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Proof depends on

- [Randomized $O(\log^2 k)$-competitive k-server on HSTs](k-server-on-hst-log-squared.md)
- [Competitive ratios transfer through dominating tree embeddings](../metrical-task-systems-and-hst-embeddings/embedding-transfer.md)
- [Fakcharoenphol-Rao-Talwar O(log n) expected-stretch tree embeddings](../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/johnson-lindenstrauss-optimality-and-metric-embeddings/frt-logarithmic-stretch-tree-embedding.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085.
- Nikhil Bansal, Niv Buchbinder, Aleksander Mądry, Joseph Naor, "A Polylogarithmic-Competitive Algorithm for the k-Server Problem", Journal of the ACM 62(5) (2015); FOCS (2011).
