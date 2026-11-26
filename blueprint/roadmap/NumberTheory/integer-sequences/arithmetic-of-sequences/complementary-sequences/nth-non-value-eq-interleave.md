# Complementary sequences from an interleaving function

Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all $m \ge 1$,
and for $n \ge 1$ let $f_P(n)$ be the $n$-th positive integer that is not a value $f(m)$ with
$m \ge 1$. Let $\alpha : \mathbb{N} \to \mathbb{R}$ satisfy $f(m - 1) \le \alpha(m) \le f(m)$ for
all $m \ge 2$, and let $h : \mathbb{N} \to \mathbb{N}$ satisfy $h(n) \ge 1$ and
$\alpha(h(n)) \le n < \alpha(h(n) + 1)$ for all $n \ge 1$.
Then for every $n \ge 1$, $f_P(n) = n + h(n) + 1$ if $f(h(n) + 1) \le n + h(n)$; otherwise
$f_P(n) = n + h(n) - 1$ if $n + h(n) \le f(h(n))$, and $f_P(n) = n + h(n)$ if not.

For increasing $\alpha$ with $\alpha(1) = 1$, the paper's choice of $h(n)$ as the largest
$m \ge 1$ with $\alpha(m) \le n$ satisfies the hypothesis on $h$.

## Sources

- Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95, Theorem 3.
