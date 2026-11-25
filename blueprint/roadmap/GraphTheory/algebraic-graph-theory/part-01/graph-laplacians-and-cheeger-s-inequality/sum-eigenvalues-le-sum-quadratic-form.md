# Hall's spectral drawing is optimal

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to [0, \infty)$, [Laplacian](laplacian.md) $L$ and eigenvalues $\lambda_1 \le \lambda_2 \le \dots \le \lambda_n$, $n = \lvert V\rvert$, listed with multiplicity (so $\lambda_1 = 0$). Let $k$ be a natural number with $k + 1 \le n$ and let $x_1, \dots, x_k : V \to \mathbb{R}$ be orthonormal vectors, each orthogonal to the constant vector. Then

$$\lambda_2 + \lambda_3 + \dots + \lambda_{k+1} \le \sum_{i=1}^{k} x_i^{\mathsf T} L x_i$$

(D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Theorem 3.2.1, which assumes $\lambda_1 < \lambda_2$, that is, a connected graph; the inequality holds without it, and the source's equality clause is a separate statement). Since $\sum_i x_i^{\mathsf T} L x_i = \sum_e w_e \lVert X(e^-) - X(e^+)\rVert^2$ for the drawing $X(a) = (x_1(a), \dots, x_k(a))$, the bottom nontrivial eigenvectors give a drawing of least total squared edge length.
