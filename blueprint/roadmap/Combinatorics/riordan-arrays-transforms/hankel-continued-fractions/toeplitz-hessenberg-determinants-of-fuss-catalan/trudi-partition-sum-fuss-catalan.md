# Trudi multi-sums of Fuss–Catalan numbers

For $s \in \mathbb{Q}$ and rational numbers
$a_1, \dots, a_n$ let $T_s(a_1, \dots, a_n)$ be the sum of
$s^{|\alpha|} \binom{|\alpha|}{\alpha_1, \dots, \alpha_n} a_1^{\alpha_1} \cdots a_n^{\alpha_n}$
over all $(\alpha_1, \dots, \alpha_n) \in \mathbb{N}^n$ with
$\alpha_1 + 2 \alpha_2 + \dots + n \alpha_n = n$, where $|\alpha| = \alpha_1 + \dots + \alpha_n$.
Let $A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$ be the generalized Fuss–Catalan number,
taken to be $0$ when $pn + r = 0$; let $C_n$ be the $n$-th Catalan number,
$K_m = C_{m+2} - C_{m+1}$ for $m \ge -1$ (so $K_{-1} = 0$), $H_n = A_n(3, 1)$ and
$J_n = A_n(3, 2)$. Then the following hold.
(1) For all natural numbers $p, r$ and every $n \ge 1$,
$-T_{-1}(A_1(p, r), \dots, A_n(p, r)) = \frac{r}{n} \binom{pn - r - 1}{n - 1}$, where the
binomial coefficient has an integer, possibly negative, upper index:
$\binom{x}{k} = x (x - 1) \cdots (x - k + 1)/k!$.
(2) For every $n \ge 1$, $-T_{-1}(K_{-1}, K_0, \dots, K_{n-2}) = \sum_{i=1}^{n-1} C_i$.
(3) For every $n \ge 1$, $-T_{-1}(K_0, K_1, \dots, K_{n-1}) = \sum_{i=0}^{n-1} C_i$.
(4) For every $n \ge 2$, $-T_{-1}(H_2, H_3, \dots, H_{n+1}) = \frac{2}{n} \binom{3n - 3}{n - 1}$.
(5) For every $n \ge 1$, $T_1(J_0, J_1, \dots, J_{n-1}) = H_n$.

Identity (1) includes $p = r = 0$, which the paper's standing assumption excludes; there both
sides are $0$.

## Sources

- Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Corollary 9 (`jis-2026-26.1.2-cor-9`).
