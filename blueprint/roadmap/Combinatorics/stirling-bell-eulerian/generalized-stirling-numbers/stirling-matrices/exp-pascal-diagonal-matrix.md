# Exponential of a Pascal diagonal matrix

Let $k \ge 1$ and $n \ge 0$. For $m \ge 0$ let
$\mathsf{L}_{d^{(m)}}(n)$ be the $n \times n$ real matrix whose $(b + m, b)$ entry is
$\binom{m+b}{b}$ for each $b$ with $b + m < n$ and whose other entries are $0$ (indices from
$0$). Let $\alpha^{(k)} = (\alpha^{(k)}_i)_{i \ge 1}$ be given by $\alpha^{(k)}_1 = 1$,
$\alpha^{(k)}_i = 0$ for $2 \le i \le k$ and
$\alpha^{(k)}_i = \binom{i-2}{k-1} \alpha^{(k)}_{i-k}$ for $i > k$, and let
$T_{\alpha^{(k)}, \beta}(n)$ be the $n \times n$ lower triangular Toeplitz matrix with first
column $\alpha^{(k)}$ and first row $\beta = (1, 0, 0, \ldots)$, that is, with $(a, b)$ entry
$\alpha^{(k)}_{a-b+1}$ for $b \le a$ and $0$ for $b > a$. Then $\exp(\mathsf{L}_{d^{(k)}}(n))$
equals the Hadamard (entrywise) product
$T_{\alpha^{(k)}, \beta}(n) \odot \sum_{i=0}^{n-1} \mathsf{L}_{d^{(ki)}}(n)$.

The paper sums over all $i \ge 0$; the terms with $i \ge n$ are zero matrices, since then
$ki \ge n$.

## Sources

- A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3 (`jis-2026-26.5.4-thm-3`).
