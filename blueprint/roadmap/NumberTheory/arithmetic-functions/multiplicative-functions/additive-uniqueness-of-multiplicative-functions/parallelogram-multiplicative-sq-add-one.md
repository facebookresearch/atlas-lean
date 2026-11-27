# Parallelogram induction: the value at p² + 1

Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p$ is odd and $f(p) = p^2$, then $f(p^2 + 1) = (p^2 + 1)^2$.

The hypothesis $p \ne 2$ is needed: the function with $f(n) = 0$ if $4 \mid n$, $f(n) = 4$ if
$n \equiv 2 \pmod 4$ and $f(n) = 1$ otherwise satisfies the hypotheses for $p = 2$, but
$f(5) = 1$.

## Sources

- Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative Functions*, INTEGERS 24 (2024), Article A108, Lemma 1.
