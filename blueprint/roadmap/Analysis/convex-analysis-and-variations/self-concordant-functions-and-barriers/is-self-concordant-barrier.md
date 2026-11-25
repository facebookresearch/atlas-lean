# Self-concordant barrier

Let $Q$ be a nonempty open convex set in a real normed space and $\vartheta \ge 0$. A function $F$ is a **$\vartheta$-self-concordant barrier** for the closed convex domain $\overline{Q}$ (with interior $Q$) if $F$ is [self-concordant](is-self-concordant.md) on $Q$ and

$$
\big|DF(x)[h]\big| \le \vartheta^{1/2}\,\big(D^2F(x)[h, h]\big)^{1/2} \qquad \text{for all } x \in Q,\ h \in E,
$$

that is, the Newton decrement of $F$ is at most $\vartheta^{1/2}$ everywhere. Here $D^kF(x)[h, \ldots, h]$ denotes the $k$-th derivative at $t = 0$ of the restriction $t \mapsto F(x + t h)$ of $F$ to the line through $x$ in direction $h$, and $|h|_x = (D^2F(x)[h, h])^{1/2}$ is the local norm defined by $F$ at $x$. The parameter $\vartheta$ governs the complexity of path-following interior-point methods: a domain with a $\vartheta$-self-concordant barrier can be optimized over to accuracy $\epsilon$ in $O(\sqrt{\vartheta} \log(1/\epsilon))$ Newton steps.

## Sources

- A. Nemirovski, *Interior Point Polynomial Time Methods in Convex Programming*, lecture notes (Georgia Tech, 2004); author PDF at <https://www2.isye.gatech.edu/~nemirovs/Lect_IPM.pdf>, Definition 3.1.1, where the barrier is defined on the interior $\operatorname{int} G$ of a closed convex domain $G$; here $Q$ plays the role of $\operatorname{int} G$. The complexity bound is Theorem 4.4.1 and Section 4.6 there, not formalized here.
