# Majority Is Stablest

Fix $0 < \rho < 1$. For every $\varepsilon > 0$ there is $\tau > 0$ such that every
$f : \{-1, 1\}^n \to [-1, 1]$ with $\mathbb{E}[f] = 0$ and $\mathrm{Inf}_i[f] \le \tau$ for all $i$
satisfies

$$\mathrm{Stab}_\rho[f] \le \frac{2}{\pi} \arcsin \rho + \varepsilon = 1 - \frac{2}{\pi} \arccos\rho + \varepsilon.$$

The source writes the error as $o_\tau(1)$. The bound is tight: it is the limit of
$\mathrm{Stab}_\rho[\mathrm{Maj}_n]$ over odd $n$ (Theorem 2.45). The theorem gives the
Unique-Games hardness of approximating Max-Cut beyond the Goemans–Williamson ratio
(Khot–Kindler–Mossel–O'Donnell) and the optimal noise stability of majority among low-influence
voting rules.

## Sources

- E. Mossel, R. O'Donnell and K. Oleszkiewicz, "Noise stability of functions with low influences:
  invariance and optimality", *Ann. of Math.* 171 (2010), 295–341 (arXiv:math/0503503),
  Theorem 4.4 in a more general form.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Majority Is Stablest Theorem, Section 5.2; proved in Chapter 11 via the Invariance
  Principle and Borell's Isoperimetric Theorem.

## Background

- [Sheppard's arcsine formula](../../../Probability/distributions/continuous/multivariate-normal-distribution/sheppard-quadrant-probability-arcsine.md):
  Sheppard's Formula gives the value $\frac{2}{\pi} \arcsin\rho$ of the limit of
  $\mathrm{Stab}_\rho[\mathrm{Maj}_n]$.
