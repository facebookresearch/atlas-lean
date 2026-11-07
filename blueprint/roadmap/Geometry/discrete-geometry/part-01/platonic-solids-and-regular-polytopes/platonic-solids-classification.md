# Classification of the Platonic solids

Let $V, E, F, p, q$ be natural numbers with
$V, E, F > 0$ and $p, q \ge 3$, and let $l > 0$ and $d > 0$ be real numbers. Let
$x_0, \dots, x_{V-1}$ be points of the Euclidean space $\mathbb{R}^3$, let $K$ be their convex
hull and let $\partial K$ be its topological boundary. Let each edge $e < E$ be an ordered pair
$(a_e, b_e)$ of point indices, with segment $[x_{a_e}, x_{b_e}]$, and let each face $f < F$ be a
list $\phi_f(0), \dots, \phi_f(p-1)$ of point indices, read cyclically: positions are taken
modulo $p$, the sides of $f$ are the pairs $(\phi_f(i), \phi_f(i+1))$, and the filled face is
the convex hull of $x_{\phi_f(0)}, \dots, x_{\phi_f(p-1)}$. An edge $e$ lies on side $i$ of $f$
when $(a_e, b_e)$ equals $(\phi_f(i), \phi_f(i+1))$ or $(\phi_f(i+1), \phi_f(i))$. Assume:
$K$ is convex and contains every $x_i$; no $x_i$ lies in the convex hull of the $x_j$ with
$j \ne i$; the differences $x_i - x_j$ span a space of dimension $3$; every edge segment has
length $l$; for every face $f$ and position $i$,
$\operatorname{dist}(x_{\phi_f(i)}, x_{\phi_f(i+1)}) = l$ and
$\operatorname{dist}(x_{\phi_f(i-1)}, x_{\phi_f(i+1)}) = d$; the indices
$\phi_f(0), \dots, \phi_f(p-1)$ of each face are distinct; no vertex $x_{\phi_f(k)}$ of a face
lies in the convex hull of the other vertices of that face; two sides $(i_1, i_1+1)$ and
$(i_2, i_2+1)$ of a face whose four endpoint positions are all different have disjoint
segments; some edge lies on each side of every face, and every edge lies on a side of some face;
every edge lies on a side of exactly two faces; every edge segment and every filled face is
contained in $K$; the differences of the vertices of each face span a space of dimension at
most $2$; for every face $f$ there are a nonzero vector $n$ and a real $c$ with
$\langle n, x \rangle \le c$ for all $x \in K$ and $\langle n, x_{\phi_f(i)} \rangle = c$ for
every position $i$; two edges $e_1, e_2$ with $(a_{e_1}, b_{e_1})$ equal to
$(a_{e_2}, b_{e_2})$ or $(b_{e_2}, a_{e_2})$ are equal; two faces with the same set of indices
are equal; every $x_i$, every edge segment and every filled face is contained in $\partial K$;
every point of $\partial K$ lies in some filled face; every point index occurs in exactly $q$
faces; and $2E = pF$, $2E = qV$ and $V - E + F = 2$. Then $(p, q, V, E, F)$ is one of
$(3, 3, 4, 6, 4)$ (tetrahedron), $(4, 3, 8, 12, 6)$ (cube), $(3, 4, 6, 12, 8)$ (octahedron),
$(5, 3, 20, 30, 12)$ (dodecahedron) or $(3, 5, 12, 30, 20)$ (icosahedron).

Conversely, each of these five tuples $(p, q, V, E, F)$ is realized: there are points, edges,
faces and reals $l, d > 0$ satisfying all the conditions above, except that the points, edge
segments and filled faces are required to lie in $\partial K$ but not separately in $K$.

Euler's relation $V - E + F = 2$ and the incidence counts $2E = pF$, $2E = qV$ are hypotheses,
and the classification is up to the tuple $(p, q, V, E, F)$, not up to congruence. Together they
give $1/p + 1/q > 1/2$, which leaves the five tuples; explicit coordinates realize each one.

## Sources

- https://en.wikipedia.org/wiki/Platonic_solid.
