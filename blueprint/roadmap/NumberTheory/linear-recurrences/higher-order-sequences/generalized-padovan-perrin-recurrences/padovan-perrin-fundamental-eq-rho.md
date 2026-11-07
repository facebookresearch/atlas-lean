# Fundamental Padovan–Perrin solutions as shifted coefficients $\rho$

Let $R$ be a
commutative ring, let $k_1, k_2 \in R$, let $p \ge 1$ and $s$ be natural numbers, and let $j$
satisfy $p + 1 \le j \le s + p - 1$. For $1 \le \ell \le s + p$ let $v^{(\ell)}$ be the solution of
the $([k]; p; s)$-Padovan–Perrin recurrence with $v^{(\ell)}(m) = 1$ if $m + 1 = \ell$ and
$v^{(\ell)}(m) = 0$ otherwise, for $0 \le m < s + p$. Let $\rho(N, s + p)$ be the Padovan–Perrin
coefficient: $0$ for $N < s + p$, and for $N \ge s + p$ the sum of $\binom{a+b}{a} k_1^a k_2^b$
over all $a, b \ge 0$ with $s a + (s + p) b = N - (s + p)$. Then for every $n \ge 0$,

$$v^{(j)}(n) = v^{(s+p)}(n + s + p - j) = \rho(n + s + p - j + 1, s + p).$$

The paper's second clause $v^{(j)}(n) = k_2\,\rho(n + j + 1, s + p)$ for $1 \le j \le p$ is
omitted: it fails for $k_1 = 1$, $k_2 = 2$, $p = 1$, $s = 2$, $j = 1$, $n = 0$, where
$v^{(1)}(0) = 1$ but $2\rho(2, 3) = 0$.

## Sources

- Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino, *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24 (2024), Article A49, Proposition 5 (`integers-2024-A49-prop-5`).
