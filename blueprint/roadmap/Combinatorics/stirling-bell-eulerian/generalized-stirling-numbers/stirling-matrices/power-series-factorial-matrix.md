# Factorial matrix of a power series

Let $K$ be a field, let $f$ be a formal power series
over $K$ in the variable $t$, and let $n$ be a natural number. The factorial matrix $M_n(f)$ is
the $n \times n$ matrix over $K$ whose entry in row $a$ and column $b$ (counted from $0$) is
$(a! \cdot 1_K) / (b! \cdot 1_K)$ times the coefficient of $t^{a-b}$ in $f$ when $b \le a$, and
$0$ when $b > a$. Here the quotient is taken in $K$ and is read as $0$ when $b! \cdot 1_K = 0$,
which can happen only in positive characteristic. When $K$ has characteristic zero, the factor is
the integer $a!/b!$ and $M_n(f)$ is the leading $n \times n$ section of the infinite lower
triangular matrix $M(f)$ of Moghaddamfar, Salehy and Salehy.

## Sources

- A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3.
