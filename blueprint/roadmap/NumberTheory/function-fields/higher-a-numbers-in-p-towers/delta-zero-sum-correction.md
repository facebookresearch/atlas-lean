# The correction term $F_y$ for sums of $\delta_0$

For natural numbers $p$, $d$ and $e$
and a rational number $y$, let $\delta_0$ be the variant of the rounding indicator for $p$ and
$d$, let $\tau_D$ be the denominator in lowest terms of $\tau = (p + 1)/d$ (with $\tau = 0$ when
$d = 0$), and let $m = \lfloor y p^e \rfloor \bmod \tau_D p$, where $\lfloor y p^e \rfloor$ is
read as $0$ when $y p^e < 0$. Define

$$F_y(e) = \sum_{k=1}^{m} \left(\delta_0(k) - \frac12 \left(1 - \frac1p\right)
\left(1 - \frac1{\tau_D}\right)\right),$$

with the conventions that $1/0 = 0$ and that reduction modulo $0$ is the identity (both matter
only when $p = 0$).

In Lemma 9 this is used with $y = x^{-1}$, written $F_{x^{-1}}$.

## Sources

- Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Lemma 9 (`F_{x^{-1}}`).
