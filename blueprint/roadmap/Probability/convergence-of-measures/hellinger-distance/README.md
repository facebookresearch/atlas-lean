# Hellinger distance

For finite measures $\mu$ and $\nu$ on the same measurable space (in practice probability measures), the Hellinger distance is

$$d_{\mathrm{Hell}}(\mu, \nu) = \Big(\frac12 \int \Big(\sqrt{\tfrac{d\mu}{d\zeta}} - \sqrt{\tfrac{d\nu}{d\zeta}}\Big)^2 \, d\zeta\Big)^{1/2}, \qquad \zeta = \mu + \nu,$$

and any other $\sigma$-finite measure $\zeta$ with respect to which both $\mu$ and $\nu$ have (almost everywhere finite) densities gives the same value. With the factor $\tfrac12$ (the normalisation of Dashti and Stuart) the distance between probability measures lies in $[0, 1]$. The formula is used only for finite measures: for infinite ones the integral can diverge and the value carries no meaning.

## Idea

The distance compares square roots of densities. For probability measures with densities $f$ and $g$ against such a $\zeta$ it equals $\big(1 - \int \sqrt{fg} \, d\zeta\big)^{1/2}$; for the normal laws $N(a, 1)$ and $N(b, 1)$ this gives $d_{\mathrm{Hell}}^2 = 1 - e^{-(a - b)^2/8}$. It is equivalent to the total variation distance, $d_{\mathrm{TV}}/\sqrt2 \le d_{\mathrm{Hell}} \le d_{\mathrm{TV}}^{1/2}$, but unlike total variation it controls differences of expectations of unbounded functions with finite second moments: $\|\mathbb{E}^\mu f - \mathbb{E}^\nu f\|$ is at most $2 (\mathbb{E}^\mu \|f\|^2 + \mathbb{E}^\nu \|f\|^2)^{1/2} d_{\mathrm{Hell}}(\mu, \nu)$. This is why it is the metric in which Bayesian posteriors are shown to depend continuously on the data and on approximations of the forward model: a Hellinger bound on posteriors passes to posterior means and, when fourth moments are finite, to posterior covariances.

## Statements

- [Hellinger distance](hellinger-dist.md)
- [Hellinger distance through densities against any dominating measure](hellinger-dist-with-density.md): formula through densities against a σ-finite dominating measure
- [The Hellinger distance is nonnegative](hellinger-dist-nonneg.md): basic property
- [The Hellinger distance from a measure to itself is zero](hellinger-dist-self.md): basic property
- [The Hellinger distance is symmetric](hellinger-dist-comm.md): basic property: symmetry
- [The Hellinger distance between probability measures is at most one](hellinger-dist-le-one.md): basic property for probability measures
- [Hellinger is at most the square root of total variation](hellinger-dist-le-sqrt-total-variation-d.md): comparison with total variation (upper bound)
- [Total variation is at most √2 times Hellinger](total-variation-dist-div-sqrt-two-le-hel.md): comparison with total variation (lower bound)
- [The Hellinger distance controls expectations](norm-integral-sub-integral-le-hellinger.md): control of differences of expectations

## Background

- [Total variation distance](../total-variation-distance/README.md): the other distance used for posterior stability; for probability measures $d_{\mathrm{TV}}/\sqrt2 \le d_{\mathrm{Hell}} \le d_{\mathrm{TV}}^{1/2}$ (Dashti and Stuart).

## Related topics

- [Total variation and Pinsker's inequality](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/README.md): the comparison of total variation with the Kullback–Leibler divergence.
- [Bayesian inverse problems](../../bayesian-statistics/bayesian-inverse-problems/README.md): posteriors are Lipschitz in the data, and stable under approximation of the forward model, in the Hellinger distance.

## Sources

- M. Dashti and A. M. Stuart, *The Bayesian Approach to Inverse Problems*, in *Handbook of Uncertainty Quantification*, Springer (2017).
