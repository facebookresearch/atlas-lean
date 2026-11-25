# The computed convex hull equals the convex hull

Let $P$ be a list of real plane points in strictly increasing lexicographic order, containing
three noncollinear points. Andrew's monotone chain algorithm builds the lower and upper chains
by keeping only strict left turns. Its output $V$ has at least three vertices, and the set of its
vertices is exactly the set of extreme points of the convex hull $\operatorname{conv}(P)$.

For each consecutive pair $a,b$ in $V$, including the last-to-first edge, take the closed
half-plane defined by $(b-a)\times(x-a)\ge 0$, where $\times$ is the planar cross product.
The intersection of these half-planes equals $\operatorname{conv}(P)$. Non-strict inequalities
include the boundary edges and vertices.

The edge inequalities contain every input point. Conversely, if a point lay in the region
but outside the convex hull of the returned vertices, a separating linear functional would
attain its maximum over the vertices at a strict corner. The two incident edges constrain the
point to directions from that corner in which the functional cannot increase.

## Sources

- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
