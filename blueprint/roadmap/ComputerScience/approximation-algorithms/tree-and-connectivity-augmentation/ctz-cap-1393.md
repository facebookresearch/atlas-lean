# Cecchetto-Traub-Zenklusen: unweighted connectivity augmentation is 1.393-approximable

There is a polynomial-time $1.393$-approximation algorithm for the (unweighted) connectivity augmentation problem, for every $k \ge 1$; in particular also for TAP. This improves the factor $1.91$ for CAP and the factor $1.458$ for TAP of Grandoni, Kalaitzis and Zenklusen. Moreover, when the ratio between the largest and smallest link weight is bounded by a constant, the same approach yields approximation factors below $1.5$ for the weighted problems.

## Proof sketch

First transfer TAP techniques to cactus augmentation by showing that, after a suitable decomposition, each cactus can be handled like a tree with stars of links. Then run a relative greedy procedure over bounded-size components, starting from an optimal solution of a covering problem with a factor-$2$ structure. A new analysis that balances the contribution of components against the remaining starting solution, rather than the classical $1+\ln 2$ integral, gives the factor $1.393$.

## Depends on

- [Weighted connectivity augmentation problem (WCAP)](connectivity-augmentation.md)
- [Augmenting odd edge-connectivity reduces to tree augmentation](odd-cap-reduces-to-tap.md)
- [Relative greedy algorithms for weighted tree augmentation](relative-greedy-augmentation.md)
- [Byrka-Grandoni-Jabal Ameli: unweighted connectivity augmentation is 1.91-approximable](bgj-cap-below-two.md)

## Proof depends on

- [Augmenting odd edge-connectivity reduces to tree augmentation](odd-cap-reduces-to-tap.md)
- [Relative greedy algorithms for weighted tree augmentation](relative-greedy-augmentation.md)

## Sources

- Federica Cecchetto, Vera Traub, Rico Zenklusen, "Bridging the Gap Between Tree and Connectivity Augmentation: Unified and Stronger Approaches", STOC (2021), arXiv:2012.00086.
- Fabrizio Grandoni, Christos Kalaitzis, Rico Zenklusen, "Improved Approximation for Tree Augmentation: Saving by Rewiring", STOC (2018).
