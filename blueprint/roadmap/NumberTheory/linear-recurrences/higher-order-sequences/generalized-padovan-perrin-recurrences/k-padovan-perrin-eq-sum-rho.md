# Combinatorial formula for the $k$-Padovan–Perrin numbers

Let $R$ be a commutative ring,
let $k \in R$, and let $v \colon \mathbb{N} \to R$ satisfy $v(n + 3) = v(n + 1) + k\,v(n)$ for
every $n$, that is, $v$ solves the Padovan–Perrin recurrence with $k_1 = 1$, $k_2 = k$, $p = 1$,
$s = 2$. Let $\rho(m) = \rho(m, 3)$ be the Padovan–Perrin coefficient for these parameters:
$\rho(m) = 0$ for $m < 3$, and for $m \ge 3$ it is the sum of $\binom{a+b}{a} k^b$ over all
$a, b \ge 0$ with $2a + 3b = m - 3$. Then for every $n \ge 3$,

$$v(n) = \rho(n)\,(k\,v(0) + v(1)) + (k\,v(1) + v(2))\,\rho(n - 1) + k\,v(2)\,\rho(n - 2).$$

The paper prints the middle coefficient as $k\,v(1)$; the coefficient $k\,v(1) + v(2)$ is the one
its Theorem 3 gives, and the printed form fails for $k = 2$, $(v(0), v(1), v(2)) = (0, 0, 1)$,
$n = 4$, where $v(4) = 1$ but the printed right side is $0$. The paper takes $k \ge 2$ an integer.

## Sources

- Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino, *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24 (2024), Article A49, Proposition 8.
