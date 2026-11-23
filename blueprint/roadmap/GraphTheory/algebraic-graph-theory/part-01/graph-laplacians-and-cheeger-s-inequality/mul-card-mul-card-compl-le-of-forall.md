# Easy direction of Cheeger's inequality

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to \mathbb{R}$ and [Laplacian](laplacian.md) $L$. Let $\lambda$ be a real number with $\lambda\, x^{\mathsf T} x \le x^{\mathsf T} L x$ for every $x : V \to \mathbb{R}$ with $\sum_v x(v) = 0$ (for nonnegative weights and $\lvert V\rvert \ge 2$, Courant–Fischer makes the second-smallest Laplacian eigenvalue the best such bound). Then for every $S \subseteq V$,

$$\lambda\, \lvert S\rvert\, \lvert V \setminus S\rvert \le \lvert V\rvert\, w(\partial S),$$

where $w(\partial S)$ is the total weight of the [cut](../../../graph-families-and-operations/finite-multigraphs/cut.md) of $S$. With $s = \lvert S\rvert/\lvert V\rvert$ this is $w(\partial S)/\lvert S\rvert \ge \lambda (1 - s)$ for nonempty $S$, D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Theorem 20.1.1 (stated there for unit weights); in particular, for nonnegative weights, $\theta_G \ge \lambda/2$.
