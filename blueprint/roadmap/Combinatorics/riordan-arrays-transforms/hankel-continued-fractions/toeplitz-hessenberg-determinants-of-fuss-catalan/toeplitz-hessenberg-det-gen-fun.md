# Generating function of Toeplitz–Hessenberg determinants

Let $R$ be a commutative ring and
$a_0, a_1, a_2, \dots$ a sequence in $R$. Write $\det(a_0; a_1, \dots, a_n)$ for the determinant
of the $n \times n$ Toeplitz–Hessenberg matrix whose entry in row $i$ and column $j$ is
$a_{i+1-j}$ for $j \le i + 1$ and $0$ above the superdiagonal. In the ring of formal power series
over $R$ let $f(x) = \sum_{n \ge 1} \det(a_0; a_1, \dots, a_n)\, x^n$ and
$H(x) = \sum_{i \ge 1} a_i (-a_0)^{i-1} x^i$. Then $f = H + H f$.

When $a_0$ is invertible, $H(x) = -g(-a_0 x)/a_0$ with $g(x) = \sum_{i \ge 1} a_i x^i$, and the
identity is the paper's $f(x) = (-g(-a_0 x)/a_0)/(1 + g(-a_0 x)/a_0)$. The form $f = H + H f$
needs no hypothesis on $a_0$; for $a_0 = 0$ it gives $\det(0; a_1, \dots, a_n) = a_1^n$.

## Sources

- Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 2 (`jis-2026-26.1.2-lem-2`).
