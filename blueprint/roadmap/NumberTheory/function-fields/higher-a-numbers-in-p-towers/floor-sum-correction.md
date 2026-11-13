# The correction term $A_{x^{-1}}$ for sums of floors

For a natural number $p$, a rational
$x$ and a natural number $n$, let $x_D$ be the prime-to-$p$ part of the denominator of $x$, write
$\lbrace t \rbrace = t - \lfloor t \rfloor$ for the fractional part of $t$, and put
$y = x^{-1} p^n$ (with $y = 0$ when $x = 0$). Define

$$A_{x^{-1}}(n) = \frac12 \left(-\left(1 - \frac1{x_D}\right) + x (1 - \lbrace y \rbrace)\right)
\lbrace y \rbrace + \sum_{k=1}^{\lfloor y \rfloor \bmod x_D}
\left(\lbrace x k \rbrace - \frac12 \left(1 - \frac1{x_D}\right)\right),$$

where $\lfloor y \rfloor$ is read as $0$ when $y < 0$.

This is the periodic correction term of Proposition 4.

## Sources

- Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Proposition 4 (`A_{x^{-1}}`).
