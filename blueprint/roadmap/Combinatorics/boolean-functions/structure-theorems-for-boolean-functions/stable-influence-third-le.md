# Corollary 9.12: stable influences of Boolean functions

Let $f : \{-1, 1\}^n \to \{-1, 1\}$ and let $i$ be a coordinate. The $1/3$-stable influence of $i$,

$$\mathrm{Inf}^{(1/3)}_i[f] = \mathrm{Stab}_{1/3}[D_i f] = \sum_{S \ni i} (1/3)^{|S| - 1}\, \hat f(S)^2,$$

satisfies $\mathrm{Inf}^{(1/3)}_i[f] \le \mathrm{Inf}_i[f]^{3/2}$. If the influence of $i$ is small,
its stable influence is much smaller. The bound is tight for a dictator, where both sides are $1$.

The derivative $D_i f$ takes values in $\{-1, 0, 1\}$ and is nonzero exactly where $i$ is pivotal,
so $\|D_i f\|_{4/3}^2 = \Pr[D_i f \ne 0]^{3/2} = \mathrm{Inf}_i[f]^{3/2}$. The bound is then
small-set expansion, $\mathrm{Stab}_\rho[g] \le \|g\|_{1+\rho}^2$, at $\rho = 1/3$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Corollary 9.12, derived there from Corollary 9.8 (Section 9.2); the formula for
  $\mathrm{Inf}^{(1/3)}_i[f]$ is used in the proof of Theorem 9.28.

## Informally uses

- [Small-Set Expansion Theorem](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bool-noise-stab-le-rpow-of-indicator.md):
  the source proves the corollary from Corollary 9.8, the case $\rho = 1/3$ of small-set expansion,
  extended to $\{-1, 0, 1\}$-valued functions.
