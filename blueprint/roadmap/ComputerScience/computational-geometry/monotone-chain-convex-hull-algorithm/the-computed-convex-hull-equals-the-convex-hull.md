# The computed convex hull equals the convex hull

Let $P$ be a finite set of points in the plane, not all on one line. Andrew's monotone chain algorithm, which sorts $P$ lexicographically and builds the lower and upper chains keeping only strict left turns, returns a polygon whose vertex set is exactly the set of extreme points of the convex hull $\mathrm{conv}(P)$, and the closed region bounded by that polygon equals $\mathrm{conv}(P)$.

## Proof depends on

- [The monotone chain hull of non-collinear points turns strictly left at every vertex](convex-hull-turns-left.md)
- [The hull's vertices are input points](convex-hull-subset.md)
- [The hull polygon contains every input point](convex-hull-left-of-edges.md)

## Sources

- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
