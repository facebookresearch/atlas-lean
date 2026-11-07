# Combinatorial expression of the Padovan–Perrin sequences

Let $R$ be a commutative ring,
let $k_1, k_2 \in R$, let $p, s$ be positive integers, and let $v \colon \mathbb{N} \to R$ satisfy
$v(n + s + p) = k_1 v(n + p) + k_2 v(n)$ for every $n$. For $0 \le m \le s + p - 1$ put
$A_m = k_2 v(m) + k_1 v(m + p)$ if $m < s$ and $A_m = k_2 v(m)$ if $m \ge s$. Let $\rho(N, s + p)$
be the Padovan–Perrin coefficient: $0$ for $N < s + p$, and for $N \ge s + p$ the sum of
$\binom{a+b}{a} k_1^a k_2^b$ over all $a, b \ge 0$ with $s a + (s + p) b = N - (s + p)$. Then for
every $n \ge s + p$,

$$v(n) = \sum_{m=0}^{s+p-1} \rho(n - m, s + p)\, A_m.$$

The paper prints the constraint in $\rho$ as $s a + (s + p) b = N - (s + p - 1)$, and with it the
identity fails (for $k_1 = k_2 = 1$, $p = 1$, $s = 2$ the printed $\rho(4, 3)$ is $1$ instead of
$0$); the constraint used here is the one of the paper's general formula (12).

## Sources

- Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino, *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24 (2024), Article A49, Theorem 3 (`integers-2024-A49-thm-3`).
