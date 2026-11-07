# The factor $(x - 1)^n$ for polynomials with distinct real roots

Let $c$ be a real
number, let $s$ be a finite set of real numbers, and let $f(x) = c \prod_{r \in s} (x - r)$ in
$\mathbb{R}[x]$. For every natural number $n$, the polynomial $(x - 1)^n$ divides the polynomial

$$\sum_{i=0}^{n} (-1)^i \binom{n}{i} \prod_{0 \le k \le n,\ k \ne i} f(x^k).$$

For $c \ne 0$ and $1 \notin s$ (the paper's conditions), this polynomial is the numerator of
$Q_n(x; f) = \sum_{i=0}^{n} (-1)^i \binom{n}{i} / f(x^i)$ over the common denominator
$\prod_{k=0}^{n} f(x^k)$; for $c = 0$ or $1 \in s$ some $f(x^k)$ is zero and only the
polynomial statement remains.

## Sources

- Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*, INTEGERS 26 (2026), Article A9, Theorem 3.1 (`integers-2026-A9-thm-3-1`).
