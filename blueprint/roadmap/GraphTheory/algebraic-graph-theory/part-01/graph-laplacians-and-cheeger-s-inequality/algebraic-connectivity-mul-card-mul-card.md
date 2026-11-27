# Easy direction of Cheeger's inequality, eigenvalue form

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to [0, \infty)$, and let $\lambda_2$ be the [algebraic connectivity](algebraic-connectivity.md) of $L_w$. For every $S \subseteq V$,

$$\lambda_2\, \lvert S\rvert\, \lvert V \setminus S\rvert \le \lvert V\rvert\, w(\partial S),$$

where $w(\partial S)$ is the total weight of the [cut](../../../graph-families-and-operations/finite-multigraphs/cut.md) of $S$, the edges with exactly one endpoint in $S$. With $s = \lvert S\rvert/\lvert V\rvert$ this reads $w(\partial S)/\lvert S\rvert \ge \lambda_2 (1 - s)$ for nonempty $S$, hence the isoperimetric ratio satisfies $\theta_G \ge \lambda_2/2$ (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Theorem 20.1.1, stated there for unit weights).
