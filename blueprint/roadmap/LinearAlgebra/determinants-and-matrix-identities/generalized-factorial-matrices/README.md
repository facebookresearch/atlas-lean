# Pan's theorem on generalized factorial matrices

Let $K$ be $\mathbb{R}$ or $\mathbb{C}$, let $p$ be a positive integer, let $x_0, \dots, x_{p-1} \in K$ be pairwise distinct, and let $\alpha, \beta, \gamma$ be real. Write $(y \mid a)_n = \prod_{j=0}^{n-1} (y - ja)$ for the generalized falling factorial, and let $S(a, b, c; n, k)$ be the unified generalized Stirling numbers, defined by $(y \mid a)_n = \sum_{k=0}^{n} S(a, b, c; n, k)\,(y - c \mid b)_k$ for all $y$ and $S(a, b, c; n, k) = 0$ for $k > n$. Let $G_a$ be the $p \times p$ matrix with entries $(x_k \mid a)_i$, let $H$ have entries $(x_k - \gamma \mid \beta)_i$, and let $\mathbf{S}(a, b, c)$ have entries $S(a, b, c; i, k)$, for $0 \le i, k < p$. Then $G_\alpha = \mathbf{S}(\alpha, \beta, \gamma)\, H$; $\det G_\alpha = \det G_0 = \prod_{0 \le i < k < p} (x_k - x_i)$; $G_\alpha$ is invertible; and $G_\alpha^{-1} = G_0^{-1}\, \mathbf{S}(0, \alpha, 0)$.

## Idea

The Vandermonde matrix $(x_k^i)$ is the case $\alpha = 0$ of a generalized factorial matrix, where powers $x^i$ are replaced by falling factorials with step $\alpha$. Changing the step is a triangular change of polynomial basis, recorded by generalized Stirling numbers. Writing $G_\alpha$ as a triangular Stirling matrix times another factorial matrix therefore shows at once that its determinant is the Vandermonde product, independent of $\alpha$, and gives its inverse from the inverse of the Vandermonde matrix. The unified Stirling numbers include the Stirling numbers of both kinds and the Lah numbers as special cases.

## Statements

- [Pan's theorem on generalized factorial matrices](pan-vandermonde.md)
- [Generalized factorial matrices: decomposition, determinant and inverse](pan-vandermonde-general.md): a stronger form, with no lower bound on $p$

## Sources

- Jiaqiang Pan, "Matrix Decomposition of the Unified Generalized Stirling Numbers and Inversion of the Generalized Factorial Matrices," Journal of Integer Sequences 15 (2012), Article 12.6.6.
