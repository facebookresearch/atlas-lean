# Self-concordant function

Let $E$ be a real normed space and $Q \subseteq E$ a nonempty open convex set. A function $F \colon E \to \mathbb{R}$ is **self-concordant** on $Q$ if

- $F$ is three times continuously differentiable and convex on $Q$;
- (barrier property) $F(x_i) \to +\infty$ along every sequence $x_i \in Q$ converging to a boundary point of $Q$;
- (differential inequality) for all $x \in Q$ and all $h \in E$,

$$
\big|D^3F(x)[h, h, h]\big| \le 2\,\big(D^2F(x)[h, h]\big)^{3/2} .
$$

Here $D^kF(x)[h, \ldots, h]$ denotes the $k$-th derivative at $t = 0$ of the restriction $t \mapsto F(x + t h)$ of $F$ to the line through $x$ in direction $h$, and $|h|_x = (D^2F(x)[h, h])^{1/2}$ is the local norm defined by $F$ at $x$. The inequality says that the second derivative is Lipschitz with constant $2$ in the local metric it defines itself, a condition invariant under affine changes of coordinates, like Newton's method; the constant $2$ is a normalization making $-\log t$ self-concordant without scaling.

## Sources

- A. Nemirovski, *Interior Point Polynomial Time Methods in Convex Programming*, lecture notes (Georgia Tech, 2004); author PDF at <https://www2.isye.gatech.edu/~nemirovs/Lect_IPM.pdf>, Definition 2.0.1 (on $\mathbb{R}^n$).
