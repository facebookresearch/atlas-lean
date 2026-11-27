# Gonzalez's farthest-first traversal is a 2-approximation for metric k-center

**Farthest-first traversal** picks an arbitrary first center and then, $k - 1$ times, adds a point at maximum distance from the centers chosen so far. On every finite metric space it returns $k$ distinct centers (when $|V| \ge k$) whose radius is at most $2 r$ for every $r \ge r^*_k$; that is, it is a $2$-approximation.

## Proof sketch

If the radius exceeded $2r^*_k$, the $k$ chosen centers and the farthest remaining point would be $k + 1$ points pairwise more than $2 r^*_k$ apart, so two of them would share an optimal center, contradicting the triangle inequality (the packing lower bound).

## Depends on

- [The k-center objective](k-center-objective.md)
- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Sources

- T. F. Gonzalez, "Clustering to Minimize the Maximum Intercluster Distance", Theoretical Computer Science 38, 1985.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
