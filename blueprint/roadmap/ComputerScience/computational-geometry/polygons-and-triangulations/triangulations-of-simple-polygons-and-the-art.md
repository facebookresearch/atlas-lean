# Triangulations of simple polygons and the art gallery theorem

Every simple polygon with $n \ge 3$ vertices has a triangulation by diagonals into exactly $n - 2$ triangles, and every simple polygon with $n \ge 4$ vertices has two non-overlapping ears. A triangulation can be computed in $O(n \log n)$ time by partitioning into monotone pieces. By three-coloring the vertices of a triangulation, $\lfloor n/3 \rfloor$ guards placed at vertices suffice to see the whole polygon, and for every $n \ge 3$ some simple polygon with $n$ vertices requires $\lfloor n/3 \rfloor$ guards.

## Depends on

- [Simple polygons](simple-polygons.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
- S. Fisk, "A short proof of Chvátal's watchman theorem", *Journal of Combinatorial Theory, Series B* 24(3):374, 1978
