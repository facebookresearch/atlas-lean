# Generalized mean value theorem for Caputo derivatives

**Theorem.** Let $0<p\le 1$, and let $H \in C[r_1, r_2]$ have its [Caputo derivative](caputo-fractional-derivative.md) ${}^{C}D^{p}_{r_1} H$ with base point $r_1$ continuous on $[r_1, r_2]$. Then for every $t \in (r_1, r_2]$ there is $\zeta \in [r_1, t]$ with

$$H(t) = H(r_1) + \frac{1}{\Gamma(p+1)}\, {}^{C}D^{p}_{r_1} H(\zeta)\,(t - r_1)^p .$$

Consequently, if ${}^{C}D^{p}_{r_1} H \ge 0$ on $[r_1, r_2]$ then $H(t) \ge H(r_1)$ for all $t \in [r_1, r_2]$, and if ${}^{C}D^{p}_{r_1} H \le 0$ there then $H(t) \le H(r_1)$.

## Depends on

- [Caputo fractional derivative](caputo-fractional-derivative.md)

## Expansion

Writing $H$ through the fractional integral, $H(t) = H(r_1) + \Gamma(p)^{-1}\int_{r_1}^t (t - s)^{p-1}\, {}^{C}D^{p}_{r_1}H(s)\, ds$, and applying the integral mean value theorem with the positive weight $(t-s)^{p-1}$, whose integral is $(t-r_1)^p/p$, gives the formula, since $p\,\Gamma(p) = \Gamma(p+1)$. At $p = 1$ it is the classical mean value theorem. The comparison is with the value at the base point $r_1$ only: for $p<1$ the Caputo derivative with base point $r_1$ at time $t$ depends on the whole history on $[r_1, t]$, so a nonnegative derivative does not by itself compare $H(t_1)$ and $H(t_2)$ for $r_1 < t_1 < t_2$, and the monotonicity corollary stated in some applications needs more than this formula. In fractional compartmental models the comparison with the initial value is combined with a first-exit argument to show that the nonnegative orthant is positively invariant when ${}^{C}D^{p}_t x_i \ge 0$ whenever $x_i = 0$ and the other coordinates are nonnegative.

## Sources

- Z. M. Odibat, N. T. Shawagfeh, "Generalized Taylor's formula", Applied Mathematics and Computation 186 (2007) 286–293, <https://doi.org/10.1016/j.amc.2006.07.102>.
- M. Awais, F. S. Alshammari, S. Ullah, M. A. Khan, S. Islam, "Modeling and simulation of the novel coronavirus in Caputo derivative", Results in Physics (2020), Lemma 0.1 and Corollary 1, <https://doi.org/10.1016/j.rinp.2020.103588> (PMC7671651).
- A. N. Chatterjee, B. Ahmad, "A fractional-order differential equation model of COVID-19 infection of epithelial cells", Chaos, Solitons and Fractals 147 (2021) 110952, Theorem 1 (positivity), <https://doi.org/10.1016/j.chaos.2021.110952> (PMC8086832).
