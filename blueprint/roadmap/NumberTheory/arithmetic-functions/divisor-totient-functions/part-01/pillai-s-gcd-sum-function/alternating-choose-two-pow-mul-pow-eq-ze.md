# An alternating binomial sum vanishes

Let $k$ and $m$ be natural numbers with $k \ge 2$
and $m \ge 2^k - 1$. Then, computed in the integers,

$$\sum_{r=0}^{\min(2^k,\, m+1)} (-1)^r \binom{2^k}{r} (m + 1 - r)^k = 0.$$

Since $m + 1 \ge 2^k$, the upper limit of the sum is $2^k$.

This sum is the exponent $\ell_m$ of the paper: the coefficient of $p^{-ms}$ in
$(1 - p^{-s})^{2^k} \sum_{a \ge 0} (a + 1)^k p^{-as}$, which is why it stops at $r = m + 1$. The
paper prints the sum up to $r = 2^k$ for every $m$; that sum vanishes for every $m$, being a
$2^k$-th difference of a polynomial of degree $k$, which contradicts the paper's own
$\ell_2 = 3^k - 4^k + \binom{2^k}{2}$: for $k = m = 2$ the truncated sum is $-1$. So with the
truncation the hypothesis $m \ge 2^k - 1$ is needed. The paper's hypothesis $k \ge 2$ is kept: for
$k = 0$ the term $r = m + 1$ contributes $0^0 = 1$ rather than the coefficient of a negative
index, so the truncated sum is no longer the coefficient read off from the paper's Euler product.

## Sources

- M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 5 (`integers-2026-A70-thm-5`).
