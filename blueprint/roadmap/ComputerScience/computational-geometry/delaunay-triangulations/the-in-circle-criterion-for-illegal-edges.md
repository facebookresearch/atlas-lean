# The in-circle criterion for illegal edges

Let $p_i p_j$ be an edge shared by the triangles $p_i p_j p_k$ and $p_i p_j p_l$ of a triangulation, such that $p_i p_k p_j p_l$ is a convex quadrilateral and the four points do not lie on a common circle. *Flipping* the edge replaces $p_i p_j$ by $p_k p_l$, and the edge is *illegal* if the smallest of the six angles of the two triangles increases by the flip. Then $p_i p_j$ is illegal if and only if $p_l$ lies in the interior of the circumcircle of $p_i p_j p_k$.

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Delaunay triangulations", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides9.pdf>: the lemma that the edge $p_i p_j$ is illegal if and only if $p_l$ lies in the interior of the circle through $p_i$, $p_j$, $p_k$, with the inscribed angle theorem it rests on
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, "Maximizing Angles and Edge Flipping"
