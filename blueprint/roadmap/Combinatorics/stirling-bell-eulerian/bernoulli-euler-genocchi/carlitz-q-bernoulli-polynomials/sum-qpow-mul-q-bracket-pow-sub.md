# Sums of $q^{rk} (k)^{n-d}$ via Carlitz-type sequences

Let $q > 0$ with $q \ne 1$, let
$[x] = (q^x - 1)/(q - 1)$, and let $r$, $d$ and $n$ be natural numbers with $r \ge 1$, $d \le r$
and $d \le n$. Write $(k)_d = k(k-1)\cdots(k-d+1)$ for the falling factorial (with $(k)_0 = 1$).
Let $T_m(x)$ ($m \in \mathbb{N}$, $x \in \mathbb{R}$) be the Carlitz-type sequence with associated
sequence $a_k = (q - 1)^{d-1} (k)_d / [k + r - d]$, that is,

$$T_m(x) = (q - 1)^{-m} \sum_{k=0}^{m} (-1)^{m-k} \binom{m}{k} a_k q^{kx}$$

for all $m$ and all real $x$. Then for every natural number $N$,

$$\sum_{k=0}^{N-1} q^{rk} [k]^{n-d} = \frac{q^{(r-d)N} T_n(N) - T_n(0)}{(n)_d},$$

where $0^0 = 1$.

## Sources

- Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.4 (`integers-2026-A85-thm-2-4`).
