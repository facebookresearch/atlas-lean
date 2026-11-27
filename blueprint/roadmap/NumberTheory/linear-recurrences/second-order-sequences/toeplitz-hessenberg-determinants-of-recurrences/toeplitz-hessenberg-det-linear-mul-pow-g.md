# Generating function of Toeplitz–Hessenberg determinants with entries $(bk + c)d^k$

Let
$R$ be a commutative ring and $a, b, c, d \in R$. Put $t_0 = a$ and $t_k = (bk + c) d^k$ for
$k \ge 1$, and for $n \ge 1$ let $u_n$ be the determinant of the $n \times n$ matrix whose
$(i, j)$ entry is $t_{i-j+1}$ if $j \le i + 1$ and $0$ otherwise. Then the formal power series
$u(x) = \sum_{n \ge 1} u_n x^n$ over $R$ satisfies

$$u(x) \bigl(1 + d(2a - b - c) x + a d^2 (a - c) x^2\bigr) = d x (b + c + a c d x).$$

Since the second factor on the left has constant term $1$, this says
$u(x) = dx(b + c + acdx)/(1 + d(2a - b - c)x + ad^2(a - c)x^2)$.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Lemma 3.
