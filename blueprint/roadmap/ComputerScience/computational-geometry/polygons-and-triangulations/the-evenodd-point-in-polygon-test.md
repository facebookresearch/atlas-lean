# The even–odd point-in-polygon test

Let $P$ be a simple polygon and $q$ a point of the plane not on its boundary. Choose a ray from $q$ that passes through no vertex of $P$ (or count crossings with the half-open convention for edges). Then $q$ lies in the bounded component of the complement of the boundary of $P$ if and only if the ray crosses the boundary an odd number of times. The test uses $O(n)$ orientation predicates (signs of the direction of three points, as defined on the linked page) for a polygon with $n$ edges and relies on the Jordan curve theorem for polygons.

## Depends on

- [Simple polygons](simple-polygons.md)
- [Direction of three points](../orientation-and-segment-intersection-tests/direction.md)

## Proof depends on

- [Jordan curve theorem for polygons](jordan-curve-theorem-for-polygons.md)
- [The complement of a simple polygon has at least two components](the-complement-of-a-simple-polygon-has-at-least-two-components.md)

## Sources

- M. Galetzka and P. O. Glauner, "A simple and correct even-odd algorithm for the point-in-polygon problem for complex polygons", *Proceedings of the 12th International Joint Conference on Computer Vision, Imaging and Computer Graphics Theory and Applications (GRAPP)*, 2017, pp. 175–178, <https://doi.org/10.5220/0006040801750178>, read in the author copy arXiv:1207.3502 <https://arxiv.org/abs/1207.3502>: Section 2 (the basic even-odd algorithm: cast a ray from the point and count the edges it intersects; even means outside and odd means inside; correctness through the Jordan curve theorem; time $O(n)$ for $n$ vertices)
- J. Erickson, *Computational Topology*, lecture notes, University of Illinois, 2023, Chapter 1 (Simple polygons), <https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/01-simple-polygons.pdf>: Section 1.3 (point-in-polygon test: shoot a ray, count the crossings, report inside if and only if the count is odd; the vertical-ray crossing test with the orientation determinant), justified by the parity proof of Lemma $\ge 2$
