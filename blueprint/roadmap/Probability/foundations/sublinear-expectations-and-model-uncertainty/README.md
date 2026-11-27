# Sublinear expectations and model uncertainty

Probability under model uncertainty, after S. Peng: the primitive object is a *sublinear expectation* $\mathbb{E}$ on a space $\mathcal{H}$ of random variables (monotone, constant preserving, subadditive, positively homogeneous) rather than a single probability measure. By the Hahn–Banach theorem, $\mathbb{E}[X]$ is the maximum of $E_\theta[X]$ over a family of linear expectations, which is the uncertain family of probability models; coherent risk measures are sublinear expectations up to a sign. Distributions and independence are defined through $\mathbb{E}$ alone, and independence is no longer symmetric. The two canonical laws are the maximal distribution and the G-normal distribution, which has no mean uncertainty.

- [Sublinear expectations](sublinear-expectations/README.md)
- [Coherent risk measures](coherent-risk-measures/README.md)
- [Sublinear expectation spaces](sublinear-expectation-spaces/README.md)
- [One-dimensional G-normal distribution](g-normal-distribution/README.md)

## Related topics

- [Limit theorems under sublinear expectations](../../central-limit-theorems/limit-theorems-under-sublinear-expectations/README.md):
  Peng's law of large numbers and central limit theorem, whose limits are the maximal and G-normal
  laws defined here.
- [Backward stochastic differential equations](../../stochastic-calculus/backward-stochastic-differential-equations/README.md):
  g-expectations, the dynamically consistent nonlinear expectations on a Wiener space that
  preceded G-expectations.
- [Hahn–Banach theorem](../../../Analysis/banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/README.md):
  the extension theorem behind the representation of a sublinear expectation.
