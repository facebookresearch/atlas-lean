# The even–odd point-in-polygon test

Let $P$ be a simple polygon and $q$ a point of the plane not on its boundary. Choose a ray from $q$ that passes through no vertex of $P$ (or count crossings with the half-open convention for edges). Then $q$ lies in the bounded component of the complement of the boundary of $P$ if and only if the ray crosses the boundary an odd number of times. The test uses $O(n)$ orientation predicates (signs of the direction of three points, as defined on the linked page) for a polygon with $n$ edges and relies on the Jordan curve theorem for polygons.

## Depends on

- [Simple polygons](simple-polygons.md)
- [Direction of three points](../orientation-and-segment-intersection-tests/direction.md)

## Proof depends on

- [Jordan curve theorem for polygons](jordan-curve-theorem-for-polygons.md)
- [The complement of a simple polygon has at least two components](the-complement-of-a-simple-polygon-has-at-least-two-components.md)

## Sources

- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
- J. O'Rourke, *Computational Geometry in C*, 2nd ed., Cambridge University Press, 1998
- J. Erickson, *Computational Topology*, lecture notes, University of Illinois, 2023, Chapter 1 (Simple polygons), <https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/01-simple-polygons.pdf>: Section 1.3 (point-in-polygon test: shoot a ray, count the crossings, report inside if and only if the count is odd; the vertical-ray crossing test with the orientation determinant), justified by the parity proof of Lemma $\ge 2$
