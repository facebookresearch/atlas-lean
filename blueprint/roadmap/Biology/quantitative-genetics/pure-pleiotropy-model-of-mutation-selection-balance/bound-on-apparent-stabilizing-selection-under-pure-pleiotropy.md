# Lower bound on the width of apparent stabilizing selection under pure pleiotropy

In the [pure-pleiotropy model](stationary-cumulants-under-pure-pleiotropy.md) with $m(x, z)$ symmetric about $z = 0$, let an individual's phenotype be $P = Z + Z' + E$, where $Z, Z'$ are independent haplotype contributions with the stationary distribution and $E \sim N(0, V_E)$ is independent environmental noise, so that $V_P = V_G + V_E$. Define the apparent stabilizing selection gradient $\tilde\gamma$ as $V_P$ times the regression coefficient of log-fitness $-(X + X')$ on $P^2$, and the equivalent width of Gaussian stabilizing selection by $V_s = -V_P/(2\tilde\gamma)$. Then

$$V_s = \frac{4\kappa_{0,2}^2 + \kappa_{0,4} + V_E(V_E + 4\kappa_{0,2})}{2\kappa_{1,2}} = \frac{V_P^2 + n\mu\,\mathbb{E}_m[Z^4/S]}{V'_m}, \qquad V'_m = 2\kappa_{1,2} = 2n\mu\, \mathbb{E}_m\!\left[\frac{X Z^2}{S}\right].$$

**Exact bound.** Whenever $V'_m > 0$, dropping the nonnegative term $n\mu\,\mathbb{E}_m[Z^4/S]$ gives

$$V_s \ge \frac{V_P^2}{V'_m}, \qquad \frac{V_s}{V_P} \ge \frac{V_P}{V'_m} \ge \frac{V_E}{V'_m}.$$

**Small-effect approximation.** Since $S = 1 - e^{-X} < X$ for every $X > 0$, $V'_m = 2n\mu\,\mathbb{E}_m[XZ^2/S]$ exceeds $2n\mu\,\mathbb{E}_m[Z^2]$; only when mutations have small effects on fitness ($X \approx S$) is $V'_m \approx 2n\mu\, \mathbb{E}_m[Z^2]$. That approximation is at most $4V_m$, where $V_m$ is the mutational variance per generation and the dominance coefficient of every mutation on the trait is at most $1$, but $V'_m$ itself need not be: with trait dominance $1$ (so $2n\mu\,\mathbb{E}_m[Z^2] = 4V_m$) and constant positive $X$, $V'_m > 4V_m$, and increasing $V_E$ makes the fourth-cumulant term negligible against $V_P^2$, so $V_s < V_P^2/(4V_m)$ for large $V_E$. To first order in the fitness effects, therefore,

$$V_s \gtrsim \frac{V_P^2}{4 V_m}, \qquad \frac{V_s}{V_P} \gtrsim \frac{V_P}{4 V_m} \ge \left(\frac{4 V_m}{V_E}\right)^{-1},$$

and these become exact inequalities under the additional hypothesis $V'_m \le 4V_m$. With $V_m/V_E < 10^{-2}$ the approximation gives $V_s/V_P \gtrsim 25$, that is $\tilde\gamma \gtrsim -1/50$: pleiotropic deleterious mutations of small effect alone can produce only very weak apparent stabilizing selection on a neutral trait.

## Proof sketch

By symmetry the odd moments in $Z$ vanish, and $\mathbb{E}[E^4] = 3V_E^2$. The covariance of $-(X + X')$ with $(Z + Z' + E)^2$ equals $-2(\mathbb{E}_f[XZ^2] - \mathbb{E}_f[X]\mathbb{E}_f[Z^2]) = -2\kappa_{1,2}$. The variance of $(Z + Z' + E)^2$ equals $2\mathbb{E}_f[Z^4] + 2\mathbb{E}_f[Z^2]^2 + 2V_E(V_E + 4\mathbb{E}_f[Z^2])$, which in cumulants ($\mathbb{E}_f[Z^4] = \kappa_{0,4} + 3\kappa_{0,2}^2$) is $2(\kappa_{0,4} + 4\kappa_{0,2}^2 + V_E^2 + 4V_E\kappa_{0,2}) = 2(\kappa_{0,4} + V_P^2)$, since $V_P = 2\kappa_{0,2} + V_E$. Substituting the cumulant formula, with $V_G = 2\kappa_{0,2}$, gives $V_s$. Dropping the nonnegative term $n\mu\,\mathbb{E}_m[Z^4/S]$ gives the exact bound, and $V_P \ge V_E$ its second form. Replacing $V'_m$ by its small-effect approximation $2n\mu\,\mathbb{E}_m[Z^2] \le 4V_m$ gives the approximate forms; writing $h^2 = V_G/V_P$, they read $V_s/V_P \gtrsim (4V_m/V_E)^{-1}/(1-h^2)$. The source's Equations A21–A25 carry an extra $V_E^2$ in the numerator (they write $2V_E(V_E + 2\kappa_{0,2})$ where its own Equation A20 gives $V_E(V_E + 4\kappa_{0,2})$), which leads to its bound $V_s/V_P > (2V_m/V_E)^{-1}$ and the figure $50$; the corrected computation gives the constants above. Its Equation A24 bounds the small-effect approximation $2n\mu\,\mathbb{E}[Z^2]$ by $4V_m$, not $V'_m$ itself.

## Depends on

- [Stationary cumulants of trait and log-fitness under pure pleiotropy](stationary-cumulants-under-pure-pleiotropy.md)
- [Genetic variance under pure pleiotropy](genetic-variance-under-pure-pleiotropy.md)

## Sources

- T. Johnson and N. Barton, Theoretical models of selection and mutation on quantitative traits, *Phil. Trans. R. Soc. B* 360 (2005), 1411–1425, <https://doi.org/10.1098/rstb.2005.1667>, PMCID PMC1569515 (Section 3(c), Equations 3.3–3.4; Appendix A(b), Equations A19–A25).
