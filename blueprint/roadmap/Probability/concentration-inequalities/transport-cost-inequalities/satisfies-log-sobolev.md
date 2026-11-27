# Logarithmic Sobolev inequality

A probability measure $m$ on a metric space satisfies the logarithmic Sobolev inequality with
constant $\alpha$ if for every nonnegative Lipschitz function $f$ with $\int f \, dm = 1$,

$$(2\alpha)^+ \, \mathrm{KL}(f m \,\|\, m) \le \int_{\{f > 0\}} \frac{|\nabla f|^2}{f} \, dm,$$

both sides taken in $[0, \infty]$, where $(2\alpha)^+ = \max(2\alpha, 0)$, $|\nabla f|$ is the
[local Lipschitz constant](local-lipschitz-constant.md), and
$\mathrm{KL}(f m \,\|\, m) = \int f \log f \, dm$ is the relative entropy of the probability measure
$f m$ with respect to $m$. The right side is the Fisher information of $f m$ relative to $m$. For
the standard Gaussian measure the inequality holds with $\alpha = 1$ (Gross).

For a complete separable metric measure space and $\alpha > 0$, Gigli and Ledoux show that this
formulation is equivalent to the ones with the descending slope, with upper gradients, and with
Sobolev functions (their Proposition 5.1).

## Sources

- N. Gigli and M. Ledoux, *From log Sobolev to Talagrand: a quick proof*, Discrete and Continuous
  Dynamical Systems, Series A (2013); preprint at https://cvgmt.sns.it/paper/1689/,
  Proposition 5.1, formulation (i).
- M. Ledoux, *Heat flows, geometric and functional inequalities*, Proceedings of the International
  Congress of Mathematicians, Seoul 2014, Theorem 2.1 (Gross' inequality for the Gaussian measure,
  for smooth positive $f$).
