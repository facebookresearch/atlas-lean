# $\lambda_2$ bounds the Rayleigh quotient on vectors orthogonal to the constants

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to [0, \infty)$, [Laplacian](laplacian.md) $L$ and [algebraic connectivity](algebraic-connectivity.md) $\lambda_2$. For every $x : V \to \mathbb{R}$ with $\sum_{v} x(v) = 0$,

$$\lambda_2\, x^{\mathsf T} x \le x^{\mathsf T} L x$$

(D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Section 3.2: the Courant–Fischer theorem, Theorem 2.0.1, gives $\lambda_2 = \min_{x \perp \mathbf 1} x^{\mathsf T} L x / x^{\mathsf T} x$ because $\mathbf 1$ spans an eigenvector of $\lambda_1 = 0$).
