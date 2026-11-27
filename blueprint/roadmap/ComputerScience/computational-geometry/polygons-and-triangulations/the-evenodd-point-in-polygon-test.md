# The even–odd point-in-polygon test

Let $P$ be a simple polygon and $q$ a point of the plane not on its boundary. Choose a ray from $q$ that passes through no vertex of $P$ (or count crossings with the half-open convention for edges). Then $q$ lies in the bounded component of the complement of the boundary of $P$ if and only if the ray crosses the boundary an odd number of times. The test uses $O(n)$ orientation predicates for a polygon with $n$ edges and relies on the Jordan curve theorem for polygons.

## Depends on

- [Simple polygons](simple-polygons.md)

## Expansion

This page becomes ready once:

- Jordan curve theorem for polygons (proof prerequisite; not yet stated)

## Sources

- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
- J. O'Rourke, *Computational Geometry in C*, 2nd ed., Cambridge University Press, 1998
