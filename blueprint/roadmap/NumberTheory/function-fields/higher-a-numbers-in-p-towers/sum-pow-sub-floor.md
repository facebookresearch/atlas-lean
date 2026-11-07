# Sum of $p^n - \lfloor x i \rfloor$

Let $p$ be a prime and $x$ a positive rational with
$v_p(x) \ge 0$. Let $x_D$ be the prime-to-$p$ part of the denominator of $x$, let $D_{x^{-1}}$
and $L_{x^{-1}}$ be the delay and the period of the base-$p$ expansion of $x^{-1}$, and let
$A_{x^{-1}}(n)$ be the periodic correction of Proposition 4. Then for every natural number $n$,

$$\sum_{i=1}^{\lfloor p^n/x \rfloor} \left(p^n - \lfloor x i \rfloor\right) =
\frac{1}{2} x^{-1} p^{2n} +
\frac{1}{2} \left(x^{-1} \left(1 - \frac{1}{x_D}\right) - 1\right) p^n + A_{x^{-1}}(n),$$

and $A_{x^{-1}}(n + L_{x^{-1}}) = A_{x^{-1}}(n)$ for every natural number $n \ge D_{x^{-1}}$.

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Proposition 4 (`integers-2026-A78-prop-4`).
