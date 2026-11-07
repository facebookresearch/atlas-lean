# Multiplicativity of the factorial matrix of a power series

Let $K$ be a field of
characteristic zero, let $f$ and $g$ be formal power series over $K$ in the variable $t$, and let
$n$ be a natural number. For a power series $h$ over $K$, write $M_n(h)$ for the $n \times n$
factorial matrix of $h$, whose entry in row $a$ and column $b$ (counted from $0$) is
$\frac{a!}{b!}$ times the coefficient of $t^{a-b}$ in $h$ when $b \le a$, and $0$ otherwise. Then
$M_n(f) M_n(g) = M_n(fg)$.

Since these matrices are lower triangular and $M_n(h)$ is the leading $n \times n$ section of the
infinite matrix $M(h)$, this is equivalent to $M(f) M(g) = M(fg)$.

## Sources

- A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 5 (`jis-2026-26.5.4-lem-5`).
