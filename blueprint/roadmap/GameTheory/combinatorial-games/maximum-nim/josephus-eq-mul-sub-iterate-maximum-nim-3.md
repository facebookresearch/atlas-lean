# Logarithmic bounds for the Josephus iteration count

Let $k \ge 2$ and $n \ge 2$ be
natural numbers, let $h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ for natural numbers $x$, write
$h_k^p$ for the $p$-th iterate of $h_k$, and define the real numbers
$v = \log n / (\log k - \log(k-1))$ and $w = (\log(n+1) - \log 2) / (\log k - \log(k-1))$,
where $\log$ is the natural logarithm. Then there is a natural number $p \ge 1$ with
$\lfloor w \rfloor \le p \le \lceil v \rceil$ and $J_k(n) = nk - h_k^p(k-1)$, where $J_k$ is the
Josephus function for elimination step $k$.

The hypothesis $n \ge 2$ is needed: for $n = 1$ we have $v = 0$, so $\lceil v \rceil = 0$ and no
$p \ge 1$ satisfies $p \le \lceil v \rceil$.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Theorem 4.
