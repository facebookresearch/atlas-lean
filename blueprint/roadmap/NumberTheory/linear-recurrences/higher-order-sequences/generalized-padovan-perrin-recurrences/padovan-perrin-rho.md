# Padovan–Perrin coefficients

Let $R$ be a commutative semiring, let $k_1, k_2 \in R$ and
let $p, s, n$ be natural numbers. The coefficient $\rho(n, s + p)$ attached to $k_1, k_2, p, s$ is
$0$ when $n < s + p$; when $n \ge s + p$ it is the sum of $\binom{a + b}{a} k_1^a k_2^b$ over all
pairs of natural numbers $a, b \le n$ with $s a + (s + p) b = n - (s + p)$. For $s > 0$ the bounds
$a, b \le n$ hold automatically.

For $s > 0$ this is the coefficient $\rho(n, r)$, $r = s + p$, of the paper's general formula (12)
for the recurrence $v_n = k_1 v_{n-s} + k_2 v_{n-s-p}$. The paper's Proposition 4 prints the
constraint as $s a + (s + p) b = n - (s + p - 1)$, which contradicts its own normalization
$\rho(s + p, s + p) = 1$ for $s \ge 2$; the constraint used here is the one of formula (12).

## Sources

- Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino, *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24 (2024), Article A49, equation (12) and Proposition 4.
