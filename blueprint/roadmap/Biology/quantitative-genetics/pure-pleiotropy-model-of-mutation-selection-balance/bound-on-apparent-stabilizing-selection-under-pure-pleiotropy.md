# Lower bound on the width of apparent stabilizing selection under pure pleiotropy

In the [pure-pleiotropy model](stationary-cumulants-under-pure-pleiotropy.md) with $m(x, z)$ symmetric about $z = 0$, let an individual's phenotype be $P = Z + Z' + E$, where $Z, Z'$ are independent haplotype contributions with the stationary distribution and $E \sim N(0, V_E)$ is independent environmental noise, so that $V_P = V_G + V_E$. Define the apparent stabilizing selection gradient $\tilde\gamma$ as $V_P$ times the regression coefficient of log-fitness $-(X + X')$ on $P^2$, and the equivalent width of Gaussian stabilizing selection by $V_s = -V_P/(2\tilde\gamma)$. Then

$$V_s = \frac{4\kappa_{0,2}^2 + \kappa_{0,4} + 2V_E(V_E + 2\kappa_{0,2})}{2\kappa_{1,2}} = \frac{V_G^2 + n\mu\,\mathbb{E}_m[Z^4/S] + 2V_E V_P}{V'_m}, \qquad V'_m = 2\kappa_{1,2} = 2n\mu\, \mathbb{E}_m\!\left[\frac{X Z^2}{S}\right].$$

When mutations have small effects on fitness ($X \approx S$), $V'_m \approx 2n\mu\, \mathbb{E}_m[Z^2]$, which is at most $4V_m$, where $V_m$ is the mutational variance per generation and the dominance coefficient of every mutation on the trait is at most $1$. Hence

$$V_s > \frac{V_G^2 + 2 V_E V_P}{4 V_m}, \qquad \text{and in particular} \qquad \frac{V_s}{V_P} > \left(\frac{2 V_m}{V_E}\right)^{-1}.$$

With $V_m/V_E < 10^{-2}$ this forces $V_s/V_P > 50$, that is $\tilde\gamma > -1/100$: pleiotropic deleterious mutations alone can produce only very weak apparent stabilizing selection on a neutral trait.

## Depends on

- [Stationary cumulants of trait and log-fitness under pure pleiotropy](stationary-cumulants-under-pure-pleiotropy.md)
- [Genetic variance under pure pleiotropy](genetic-variance-under-pure-pleiotropy.md)

## Expansion

By symmetry the odd moments in $Z$ vanish, and $\mathbb{E}[E^4] = 3V_E^2$. The covariance of $-(X + X')$ with $(Z + Z' + E)^2$ equals $-2(\mathbb{E}_f[XZ^2] - \mathbb{E}_f[X]\mathbb{E}_f[Z^2]) = -2\kappa_{1,2}$. The variance of $(Z + Z' + E)^2$ equals $2\mathbb{E}_f[Z^4] + 2\mathbb{E}_f[Z^2]^2 + 2V_E(V_E + 4\mathbb{E}_f[Z^2])$, which in cumulants is $2(\kappa_{0,4} + 4\kappa_{0,2}^2 + V_E(2V_E + 4\kappa_{0,2}))$. Substituting the cumulant formula, with $V_G = 2\kappa_{0,2}$, gives $V_s$. Dropping the nonnegative fourth-moment term and bounding $V'_m \le 4V_m$ gives the inequality; then $V_G^2 + 2V_E V_P \ge 2V_E V_P$ gives the second form. Writing $h^2 = V_G/V_P$, the bound reads $V_s/V_P \gtrsim (4V_m/V_E)^{-1}\left(2 + (h^2)^2/(1-h^2)\right)$.

## Sources

- T. Johnson and N. Barton, Theoretical models of selection and mutation on quantitative traits, *Phil. Trans. R. Soc. B* 360 (2005), 1411–1425, <https://doi.org/10.1098/rstb.2005.1667>, PMCID PMC1569515 (Section 3(c), Equations 3.3–3.4; Appendix A(b), Equations A19–A25).
