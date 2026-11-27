# The complement of a simple polygon has at least two components

Let $P \subset \mathbb{R}^2$ be the boundary curve of a simple polygon. For a point $q \notin P$ that lies on no vertical line through a vertex of $P$, let $\pi(q) \in \{0, 1\}$ be the parity of the number of edges of $P$ that meet the upward vertical ray from $q$. Then $\pi$ is constant on the points where it is defined in each connected component of $\mathbb{R}^2 \setminus P$, and both values occur: points just above and just below the relative interior of a non-vertical edge have different parity. Hence $\mathbb{R}^2 \setminus P$ has at least two connected components.

After a rotation of the plane, which is a homeomorphism, no two vertices share an $x$-coordinate. The proof compares two trapezoids of the slab decomposition that share a vertical wall through a vertex $p_i$: whether the neighbours $p_{i-1}, p_{i+1}$ lie on the same or on opposite sides of the wall, the numbers of edges above the two trapezoids differ by $0$ or $2$.

## Depends on

- [Simple polygons](simple-polygons.md)

## Sources

- J. Erickson, *Computational Topology*, lecture notes, University of Illinois, 2023, Chapter 1 (Simple polygons), <https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/01-simple-polygons.pdf>: Section 1.2, Lemma $\ge 2$ and its proof by the parity of the number of polygon edges above each trapezoid
- R. E. Schwartz, "The polygonal Jordan curve theorem", lecture notes, Brown University, 2020, <http://www.math.brown.edu/reschwar/M1230/jordan.pdf>: Section 0.2, Lemma 0.5, and Section 0.3, Lemma 0.6 (a parity argument: the intersection parity $I(a, b, J)$ is well defined)
