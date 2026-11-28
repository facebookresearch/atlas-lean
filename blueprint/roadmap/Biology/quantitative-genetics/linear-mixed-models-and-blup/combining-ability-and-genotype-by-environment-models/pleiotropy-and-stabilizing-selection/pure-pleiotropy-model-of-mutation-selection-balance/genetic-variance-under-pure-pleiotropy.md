# Genetic variance under pure pleiotropy

In the [pure-pleiotropy model](stationary-cumulants-under-pure-pleiotropy.md), suppose the distribution of mutational effects $m(x, z)$ is symmetric about $z = 0$, so that the stationary trait mean is zero. A diploid breeding value $G = Z + Z'$ is the sum of two independent haplotype contributions with the stationary distribution $f$. Then

$$V_G = 2\kappa_{0,2} = 2 n \mu\, \mathbb{E}_m\!\left[\frac{Z^2}{S}\right],$$

so $V_G$ is finite if and only if $\mathbb{E}_m[Z^2/S] < \infty$. Two consequences follow.

1. If the effects on fitness and on the trait are independent under $m$, then $V_G = \dfrac{2n\mu}{\bar s_H} \mathbb{E}_m[Z^2]$, where $\bar s_H = (\mathbb{E}_m[1/S])^{-1}$ is the harmonic mean selection coefficient; if moreover $0 < \mathbb{E}_m[Z^2] < \infty$, then $V_G$ is finite if and only if $\bar s_H > 0$.
2. If, conditionally on $S = s$, $|Z| \le k \sqrt{s}\, |U|$ for a constant $k$ and a random variable $U$ independent of $s$ with $\mathbb{E}[U^2] < \infty$, then $V_G \le 2n\mu\, k^2\, \mathbb{E}[U^2] < \infty$. When $\mathbb{E}_m[Z^2] < \infty$, it suffices that this bound holds for $s$ in a neighbourhood of $0$.

The divergence of $V_G$ found for some parametric choices of $m$ as the population size grows therefore comes from the behaviour of $m$ near $s = 0$, not from the pure-pleiotropy model itself.

## Proof sketch

With zero mean, $V_G = \mathbb{E}[(Z + Z')^2] = 2\mathbb{E}_f[Z^2] = 2\kappa_{0,2}$, and the cumulant formula with $(a, b) = (0, 2)$ gives the main identity. Independence factorizes $\mathbb{E}_m[Z^2/S] = \mathbb{E}_m[Z^2]\, \mathbb{E}_m[1/S]$, and when $0 < \mathbb{E}_m[Z^2] < \infty$ this product is finite exactly when $\mathbb{E}_m[1/S] < \infty$. Under the bound, $Z^2/S \le k^2 U^2$. To localize, split $\mathbb{E}_m[Z^2/S]$ over $\{S < \epsilon\}$ and $\{S \ge \epsilon\}$; the second part is at most $\mathbb{E}_m[Z^2]/\epsilon$, finite when $\mathbb{E}_m[Z^2] < \infty$.

## Depends on

- [Stationary cumulants of trait and log-fitness under pure pleiotropy](stationary-cumulants-under-pure-pleiotropy.md)

## Sources

- T. Johnson and N. Barton, Theoretical models of selection and mutation on quantitative traits, *Phil. Trans. R. Soc. B* 360 (2005), 1411–1425, <https://doi.org/10.1098/rstb.2005.1667>, PMCID PMC1569515 (Appendix A(a)(i), Equations A15–A18).
