# Byrka-Grandoni-Jabal Ameli: unweighted connectivity augmentation is 1.91-approximable

There is a polynomial-time $1.91$-approximation algorithm for the (unweighted) connectivity augmentation problem, for every $k \ge 1$. This is the first factor below $2$ for CAP with even $k$, where the minimum cuts form a cactus rather than a tree.

## Proof sketch

Reduce to augmenting a cactus, and from there to a node-weighted Steiner tree problem: solutions of CAP correspond to Steiner trees in an auxiliary graph whose terminals are the cactus cycles' arcs, up to an additive factor controlled by the structure of crossing links. Applying a Steiner tree approximation based on iterative randomized rounding to this instance and charging the conversion back yields a factor of about $1.91$.

## Depends on

- [Weighted connectivity augmentation problem (WCAP)](connectivity-augmentation.md)
- [Augmenting odd edge-connectivity reduces to tree augmentation](odd-cap-reduces-to-tap.md)
- [Steiner tree instances](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-instance.md)

## Proof depends on

- [Augmenting odd edge-connectivity reduces to tree augmentation](odd-cap-reduces-to-tap.md)
- [Steiner tree instances](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-instance.md)

## Sources

- Jaroslaw Byrka, Fabrizio Grandoni, Afrouz Jabal Ameli, "Breaching the 2-Approximation Barrier for Connectivity Augmentation: A Reduction to Steiner Tree", STOC (2020), arXiv:1911.02259.
- Jaroslaw Byrka, Fabrizio Grandoni, Thomas Rothvoss, Laura Sanita, "Steiner Tree Approximation via Iterative Randomized Rounding", Journal of the ACM (2013).
