# Complementary sequences from one evaluation of the counting function

Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all
$m \ge 1$, let $C(x)$ be the number of $m$ with $1 \le m \le x$ and $f(m) \le x$, and for
$n \ge 1$ let $f_P(n)$ be the $n$-th positive integer that is not a value $f(m)$ with $m \ge 1$.
Then for every $n \ge 1$, $f_P(n) = n + C(n) + 1$ if $f(C(n) + 1) \le n + C(n)$, and
$f_P(n) = n + C(n)$ otherwise.

## Sources

- Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95, Theorem 2.
