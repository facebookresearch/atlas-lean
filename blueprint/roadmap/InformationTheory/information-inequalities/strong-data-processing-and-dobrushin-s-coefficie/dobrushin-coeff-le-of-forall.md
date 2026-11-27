# Sharpness of Dobrushin's coefficient

Let $\kappa$ be a Markov kernel whose input space has measurable singletons. If a constant
$c \ge 0$ satisfies $\mathrm{TV}(\kappa \circ \mu, \kappa \circ \nu) \le c\, \mathrm{TV}(\mu, \nu)$
for all probability measures $\mu$ and $\nu$, then $\eta_{\mathrm{TV}}(\kappa) \le c$: point masses
$\mu = \delta_x$, $\nu = \delta_{x'}$ give $\mathrm{TV}(\kappa(x), \kappa(x')) \le c$ for every pair, hence for the
supremum. With
[Dobrushin's contraction](total-variation-dist-comp-le.md), the best contraction constant of
$\kappa$ for total variation is exactly $\eta_{\mathrm{TV}}(\kappa)$.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 33.4 (the inequality `η_TV ≥ sup_{x ≠ x'} TV(P_{Y|X=x}, P_{Y|X=x'})`, from `P_X = δ_x`, `Q_X = δ_{x'}`).
