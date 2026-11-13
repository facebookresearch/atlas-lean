# Heilermann's formula for weighted Motzkin arrays

Let $K$ be a commutative ring, let
$\alpha$, $\beta$ be sequences in $K$, let $\mu_0 \in K$, and let $(M_{n,j})_{n, j \ge 0}$ be an
array in $K$ with $M_{0,0} = \mu_0$ and, for all $n, j \ge 0$, $M_{0,j+1} = 0$,
$M_{n+1,0} = \alpha_0 M_{n,0} + \beta_1 M_{n,1}$ and
$M_{n+1,j+1} = M_{n,j} + \alpha_{j+1} M_{n,j+1} + \beta_{j+2} M_{n,j+2}$. Then for every
$n \ge 0$ the Hankel transform of the column $(M_{m,0})_{m \ge 0}$ at $n$, the determinant of the
$(n+1) \times (n+1)$ matrix $(M_{i+j,0})_{0 \le i, j \le n}$, equals

$$\mu_0^{n+1} \prod_{j=0}^{n-1} \beta_{j+1}^{\,n-j},$$

that is, $\mu_0^{n+1} \beta_1^n \beta_2^{n-1} \cdots \beta_n$, which is $\mu_0$ for $n = 0$.

No hypothesis that the $\beta_i$ are nonzero is needed.

## Sources

- Paul Barry, *From Fibonacci to Robbins: Series Reversion and Hankel Transforms*, Journal of Integer Sequences 24 (2021), Article 21.10.2, lines 110–117, https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex.
