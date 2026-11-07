# Extended Carlitz $q$-Bernoulli numbers via $q$-Stirling numbers

Let $q > 0$ with
$q \ne 1$ be real, write $[x] = (q^x - 1)/(q - 1)$ for real $x$, $[x]_m = [x][x-1] \cdots [x-m+1]$
(with $[x]_0 = 1$) and $[m]! = [1][2] \cdots [m]$ (with $[0]! = 1$), and let $\beta_n^{(r)}(x)$
be the extended Carlitz $q$-Bernoulli polynomials, with numbers $\beta_n^{(r)} = \beta_n^{(r)}(0)$.
Let $r \ge 1$ and $n$ be natural numbers, and let $S(m, k)$ be real numbers such that
$[x]^m = \sum_{k=0}^{m} q^{k(k-1)/2} S(m, k) [x]_k$ for every natural number $m$ and every real
$x$ (the defining identity of Carlitz's $q$-Stirling numbers of the second kind). For natural $k$
put $\varphi_r(q, k) = (-1)^k [k]! \sum_{i=0}^{r-1} q^{ik} [r-1]_i / [k+r]_{i+1}$. Then

$$\beta_n^{(r)} = \sum_{k=0}^{n} \varphi_r(q, k) S(n, k),$$

and for every natural number $k$,

$$
\varphi_r(q, k) = (-1)^k [k]! \, [r-1]! \, q^{1-r} \sum_{i=0}^{r-1}
\frac{(q-1)^i q^{i(i+1)/2 - i(r-1)}}{[r-1-i]! \, [k+i+1]}.
$$

## Sources

- Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.13 (`integers-2026-A85-thm-2-13`).
