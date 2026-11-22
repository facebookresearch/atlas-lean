# Sublinear expectations and model uncertainty

Probability under model uncertainty, after S. Peng: the primitive object is a *sublinear expectation* $\mathbb{E}$ on a space $\mathcal{H}$ of random variables (monotone, constant preserving, subadditive, positively homogeneous) rather than a single probability measure. By the Hahn–Banach theorem, $\mathbb{E}[X]$ is the maximum of $E_\theta[X]$ over a family of linear expectations, which is the uncertain family of probability models; coherent risk measures are sublinear expectations up to a sign. Distributions and independence are defined through $\mathbb{E}$ alone, and independence is no longer symmetric. The two canonical laws are the maximal distribution and the G-normal distribution, which has no mean uncertainty.
- [Coherent acceptable set](is-coherent-acceptable-set.md)
- [Coherent risk measure](is-coherent-risk-measure.md)
- [The acceptance set of a coherent risk measure](is-coherent-acceptable-set-2.md)
- [Coherent risk measures give sublinear expectations](is-sublinear-expectation-2.md)
- [Coherent risk measures of constants](map-const.md)
- [Sublinear expectation](is-sublinear-expectation.md)
- [Representation of a sublinear expectation, pointwise form](exists-linear-expectation.md)
- [Sublinear expectations give coherent risk measures](is-coherent-risk-measure-2.md)
- [Representation of a sublinear expectation as a maximum of linear expectations](is-greatest.md)
- [Representation on a finite scenario set](is-greatest-finite.md)
- [Representation of a sublinear functional, pointwise form](exists-linear-le-eq.md)
- [Representation of a sublinear functional as a maximum of linear functionals](is-greatest-linear-le.md)
- [Positively homogeneous functionals vanish at zero](map-zero-of-pos-hom.md)
- [Peng's test-function class $C_{l.Lip}$](is-loc-lip.md)
- [Sublinear expectation space](sublinear-expectation-space.md)
- [Identically distributed random vectors](ident-distrib.md)
- [Independence under a sublinear expectation](indep-from.md)
- [G-normal distribution, one-dimensional](is-gnormal.md)
- [A G-normal random variable has zero upper mean](expectation-eq-zero.md)
- [A G-normal random variable has zero lower mean](expectation-neg-eq-zero.md)
- [Sums of random variables](add-mem.md)
- [Constants are random variables](const-mem.md)
- [Cash translatability](expectation-const-add.md)
- [Constants are test functions](is-loc-lip-const.md)
- [Lipschitz functions are test functions](is-loc-lip-of-lipschitz-with.md)

## Related topics

- [Limit theorems under sublinear expectations](../../central-limit-theorems/limit-theorems-under-sublinear-expectations/README.md):
  Peng's law of large numbers and central limit theorem, whose limits are the maximal and G-normal
  laws defined here.
- [Backward stochastic differential equations](../../stochastic-calculus/backward-stochastic-differential-equations/README.md):
  g-expectations, the dynamically consistent nonlinear expectations on a Wiener space that
  preceded G-expectations.
- [Hahn–Banach theorem](../../../Analysis/banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/README.md):
  the extension theorem behind the representation of a sublinear expectation.
