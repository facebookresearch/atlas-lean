# The open unit Dikin ellipsoid lies in the domain

Let $E$ be a finite-dimensional real normed space and $F$ [self-concordant](is-self-concordant.md) on $Q \subseteq E$. For every $x \in Q$, every $y$ with $|y - x|_x < 1$, i.e. $D^2F(x)[y - x, y - x] < 1$, lies in $Q$. Here $D^kF(x)[h, \ldots, h]$ denotes the $k$-th derivative at $t = 0$ of the restriction $t \mapsto F(x + t h)$ of $F$ to the line through $x$ in direction $h$, and $|h|_x = (D^2F(x)[h, h])^{1/2}$ is the local norm defined by $F$ at $x$.

So the local norm alone certifies that a Newton step of local length less than $1$ stays feasible.

## Sources

- A. Nemirovski, *Interior Point Polynomial Time Methods in Convex Programming*, lecture notes (Georgia Tech, 2004); author PDF at <https://www2.isye.gatech.edu/~nemirovs/Lect_IPM.pdf>, Section 2.2, item I ("the open unit Dikin ellipsoid $W_1(x)$ is contained in $Q$").
