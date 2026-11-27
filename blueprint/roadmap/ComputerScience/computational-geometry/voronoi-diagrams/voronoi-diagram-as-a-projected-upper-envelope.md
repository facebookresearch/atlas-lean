# Voronoi diagram as a projected upper envelope

Let $P$ be a set of $n \ge 2$ distinct points in $\mathbb{R}^2$. For $p = (a, b) \in P$ let $h(p)$ be the plane $z = 2ax + 2by - (a^2 + b^2)$ tangent to the paraboloid $z = x^2 + y^2$ above $p$. For every point $q = (x, y)$, the vertical distance from $(x, y, x^2 + y^2)$ down to $h(p)$ equals $\|q - p\|^2$, so a downward vertical ray from that point meets the planes $h(p)$ in increasing order of the distance from $q$ to $p$. Consequently the vertical projection to the $xy$-plane of the boundary complex of the upper envelope of $\{h(p) : p \in P\}$ is $\mathrm{Vor}(P)$, the face on $h(p)$ projecting onto the cell $V(p)$.

## Depends on

- [Voronoi diagram of a planar point set](voronoi-diagram.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 35, the lemma on the order of the tangent planes along a vertical ray and the theorem identifying the Voronoi diagram with the projection of their upper envelope
