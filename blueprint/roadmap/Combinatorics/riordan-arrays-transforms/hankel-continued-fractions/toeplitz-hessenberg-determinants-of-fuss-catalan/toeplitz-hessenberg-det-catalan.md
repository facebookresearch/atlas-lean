# Toeplitz–Hessenberg determinants with Catalan entries

Write $\det(a_0; a_1, \dots, a_n)$
for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix whose entry in row $i$ and
column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the superdiagonal (so $a_0$ fills the
superdiagonal and $a_1, \dots, a_n$ the first column); for $n = 0$ it is $1$. Let $C_n$ be the
$n$-th Catalan number, $C(x) = \sum_{n \ge 0} C_n x^n \in \mathbb{Q}[[x]]$, and
$K_m = C_{m+2} - C_{m+1}$ for $m \ge -1$, so that $K_{-1} = 0$. Then the following hold.
(1) $\sum_{n \ge 1} \det(-1; C_1, C_3, \dots, C_{2n-1})\, x^{2n} = x^2 C(x)^2 C(-x)^2$.
(2) $\bigl(\sum_{n \ge 0} \det(-1; C_2, \dots, C_{n+1})\, x^n\bigr) \bigl(2 - C(x)^2\bigr) = 1$.
(3) For every $n \ge 1$,
$\det(1; K_{-1}, K_0, \dots, K_{n-2}) = (-1)^{n-1} \sum_{i=1}^{n-1} C_i$.
(4) For every $n \ge 1$, $\det(1; K_0, K_1, \dots, K_{n-1}) = (-1)^{n-1} \sum_{i=0}^{n-1} C_i$.
(5) $\bigl(\sum_{n \ge 1} \det(-1; K_0, K_1, \dots, K_{n-1})\, x^n\bigr) \bigl(1 - x C(x)^3\bigr) =
x C(x)^3$.

Thus the determinants in (2) have generating function $1/(2 - C(x)^2)$ and those in (5) have
generating function $x C(x)^3/(1 - x C(x)^3)$, the generating function of OEIS A026674; the
determinants in (1) form OEIS A066357.

## Sources

- Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 6 (`jis-2026-26.1.2-thm-6`).
