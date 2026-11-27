# Toeplitz–Hessenberg determinant

Let $R$ be a commutative ring, let $a_0, a_1, a_2, \dots$
be elements of $R$ and let $n \ge 0$. The Toeplitz–Hessenberg determinant $\det A_n$ is the
determinant of the $n \times n$ matrix $A_n = A_n(a_0; a_1, \dots, a_n)$ whose entry in row $i$
and column $j$ ($0 \le i, j < n$) is $a_{i+1-j}$ if $j \le i + 1$ and $0$ otherwise. Thus $a_0$
fills the superdiagonal, $a_1$ the diagonal, and every entry above the superdiagonal is $0$. For
$n = 0$ the determinant is $1$.

## Sources

- Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Section 2, display (1) and the notation `D_±`.
