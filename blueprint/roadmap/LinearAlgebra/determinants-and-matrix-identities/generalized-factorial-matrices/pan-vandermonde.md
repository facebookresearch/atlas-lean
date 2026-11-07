# Pan's theorem on generalized factorial matrices

Let $K$ be $\mathbb{R}$ or $\mathbb{C}$,
let $p$ be a positive integer, let $x_0, \dots, x_{p-1} \in K$ be pairwise distinct, and let
$\alpha, \beta, \gamma \in \mathbb{R}$. For $y \in K$, $a \in \mathbb{R}$ and $n \in \mathbb{N}$
write $(y \mid a)_n = \prod_{j=0}^{n-1} (y - ja)$. Let numbers $S(a, b, c; n, k) \in K$, for
$a, b, c \in \mathbb{R}$ and $n, k \in \mathbb{N}$, satisfy $S(a, b, c; n, k) = 0$ whenever
$k > n$, and $(y \mid a)_n = \sum_{k=0}^{n} S(a, b, c; n, k)\,(y - c \mid b)_k$ for all
$a, b, c \in \mathbb{R}$, $y \in K$ and $n \in \mathbb{N}$. For $a, b, c \in \mathbb{R}$ let
$\mathbf{S}(a, b, c)$ be the $p \times p$ matrix with entries $S(a, b, c; i, k)$, let $G_a$
be the $p \times p$ matrix with entries $(x_k \mid a)_i$, and let $H$ be the $p \times p$
matrix with entries $(x_k - \gamma \mid \beta)_i$, where $0 \le i, k < p$. Then
$G_\alpha = \mathbf{S}(\alpha, \beta, \gamma)\, H$; $\det G_\alpha = \det G_0$;
$\det G_0 = \prod_{0 \le i < k < p} (x_k - x_i)$; $G_\alpha$ is invertible; and
$G_\alpha^{-1} = G_0^{-1}\, \mathbf{S}(0, \alpha, 0)$.

## Sources

- Jiaqiang Pan, "Matrix Decomposition of the Unified Generalized Stirling Numbers and Inversion of the Generalized Factorial Matrices," Journal of Integer Sequences 15 (2012), Article 12.6.6, Theorem (label t:Vandermonde), lines 428–460, https://cs.uwaterloo.ca/journals/JIS/VOL15/Pan/pan19.tex. It follows from `pan_vandermonde_general`; the hypothesis `hp` is unused and keeps the source's shape. Proves `Wanted` entry `pan_vandermonde`.
