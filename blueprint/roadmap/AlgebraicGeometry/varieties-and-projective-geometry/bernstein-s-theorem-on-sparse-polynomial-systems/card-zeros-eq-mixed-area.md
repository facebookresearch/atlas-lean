# Bernstein's theorem in the plane

Let $A, B \subseteq \mathbb{Z}^2$ be nonempty finite sets of exponent vectors. There is a
nonzero polynomial $D$ in the coefficients $(a_u)_{u \in A}$ and $(b_u)_{u \in B}$ such that,
whenever $D(a, b) \neq 0$, the system $g(x, y) = h(x, y) = 0$ with
$g = \sum_{u \in A} a_u x^{u_0} y^{u_1}$ and $h = \sum_{u \in B} b_u x^{u_0} y^{u_1}$ has finitely
many solutions in the torus $(\mathbb{C}^*)^2$, and their number is the mixed area
$M(P, Q) = \operatorname{area}(P + Q) - \operatorname{area}(P) - \operatorname{area}(Q)$ of the
Newton polygons $P = \operatorname{conv}(A)$ and $Q = \operatorname{conv}(B)$.

Sturmfels states the theorem for polynomials and remarks that it holds for Laurent polynomials,
the form given here. It refines Bézout's count: for dense polynomials of degrees $d$ and $e$ the
Newton polygons are triangles and the mixed area is $de$, while sparse systems can have many fewer
solutions (four instead of six in the book's running example). A consequence is that the mixed
area of two lattice polygons is a nonnegative integer.

## Sources

- Bernd Sturmfels, *Solving Systems of Polynomial Equations*, CBMS Regional Conference Series in Mathematics 97, AMS, 2002, Section 3.1, Theorem 3.2 and the remark after it.
- D. N. Bernstein, *The number of roots of a system of equations*, Functional Analysis and its Applications 9 (1975), no. 3, 183–185.
