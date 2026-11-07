# Sum of $\delta$ up to $\lfloor p^n/x \rfloor$

Let $p$ be a prime and $d$ a divisor of
$p - 1$; let $\delta$ be the rounding indicator, $\tau_D$ the denominator of $\tau = (p + 1)/d$
in lowest terms, and $F_y(e)$ the $\delta_0$ correction sum of Lemma 9. For every rational
$x \ge 1$ and every natural number $n$,

$$\sum_{i=1}^{\lfloor p^n/x \rfloor} \delta(i) =
\frac{1}{2} \left(1 - \frac{1}{\tau_D}\right) \left(p^n - \frac{1}{p}\right) x^{-1} -
\frac{1}{2} \left(1 - \frac{1}{p}\right) \left(1 - \frac{1}{\tau_D}\right)
\sum_{e=0}^{n} \left(x^{-1} p^e - \lfloor x^{-1} p^e \rfloor\right) +
\sum_{e=0}^{n} F_{x^{-1}}(e).$$

The paper's positivity of $n$ is dropped (the identity holds at $n = 0$).

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Corollary 4 (`integers-2026-A78-cor-4`).
