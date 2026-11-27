# Local complementation

Let $G$ be a simple graph and $v$ a vertex. The local complementation of $G$ at $v$ is the graph
$G * v$ on the same vertices in which two distinct vertices $x, y$ are adjacent exactly when
either $xy$ is an edge of $G$ or both $x$ and $y$ are neighbours of $v$, but not both:

$$G * v = (V, E \,\triangle\, \{xy : xv, yv \in E,\ x \ne y\}).$$

In words, the subgraph induced on the neighbourhood of $v$ is replaced by its complement; the
edges at $v$ are unchanged.

## Sources

- S. Oum, *Rank-width and vertex-minors*, J. Combin. Theory Ser. B 95 (2005) 79–100; read in the author's revised preprint of 18 April 2005 (https://sangil.dimag.kr/pdf/vertexminor-revision.pdf), whose numbering is cited here, Section 2.
- S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017) 15–24; read as arXiv:1601.03800v2 (27 July 2016), whose numbering is cited here, Section 4.1.
