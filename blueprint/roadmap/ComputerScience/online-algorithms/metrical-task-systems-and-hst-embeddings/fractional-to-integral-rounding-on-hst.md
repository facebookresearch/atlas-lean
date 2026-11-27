# Online rounding of fractional k-server on HSTs

On every $\tau$-HST with $\tau > 5$, every online fractional $k$-server algorithm (maintaining a nonnegative mass at each leaf with total mass $k$ and mass at most one per leaf, charged by transportation cost along the tree) can be converted online into a randomized integral $k$-server algorithm whose expected cost is at most $O(1)$ times the fractional cost.

## Proof sketch

Maintain a distribution over integral configurations whose marginals at each subtree equal the fractional mass rounded up or down, updating the distribution with minimal probability mass moved whenever the fractional solution moves; the separation of edge lengths guarantees that the probability mass moved at each level of the tree is paid for, up to a geometric series, by the fractional movement at that level.

## Depends on

- [Hierarchically separated trees](hierarchically-separated-tree.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Fractional k-server on a tree](../randomized-k-server-by-mirror-descent/fractional-k-server-polytope.md)

## Sources

- Nikhil Bansal, Niv Buchbinder, Aleksander Mądry, Joseph Naor, "A Polylogarithmic-Competitive Algorithm for the k-Server Problem", Journal of the ACM 62(5) (2015); FOCS (2011), arXiv:1110.1580, Section 5.2.
- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085, Lemma 3.2.
