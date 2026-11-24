# Semiboundedness of a self-concordant barrier

Let $E$ be a finite-dimensional real normed space and $F$ a $\vartheta$-[self-concordant barrier](is-self-concordant-barrier.md) for $\overline{Q}$. Then for every $x \in Q$ and every $y \in \overline{Q}$,

$$
DF(x)[y - x] \le \vartheta .
$$

Here $D^kF(x)[h, \ldots, h]$ denotes the $k$-th derivative at $t = 0$ of the restriction $t \mapsto F(x + t h)$ of $F$ to the line through $x$ in direction $h$, and $|h|_x = (D^2F(x)[h, h])^{1/2}$ is the local norm defined by $F$ at $x$. On the central path $x(t) = \operatorname{argmin}_Q \{t\, c^T x + F(x)\}$ the centrality condition $t c + F'(x(t)) = 0$ turns it into $c^T x(t) - c^T y \le \vartheta / t$ for every $y \in \overline{Q}$, the accuracy guarantee of path-following methods.

## Background

- [Duality gap of central points](../lagrange-duality/central-point-duality-gap.md): the bound $m/t$ for the logarithmic barrier of $m$ inequality constraints, the case $\vartheta = m$.

## Sources

- A. Nemirovski, *Interior Point Polynomial Time Methods in Convex Programming*, lecture notes (Georgia Tech, 2004); author PDF at <https://www2.isye.gatech.edu/~nemirovs/Lect_IPM.pdf>, Section 3.2, item I, (3.6).
