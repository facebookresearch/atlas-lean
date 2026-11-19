# Hellinger distance

The Hellinger distance $d_{\mathrm{Hell}}(\mu, \nu) = \big(\tfrac12 \int (\sqrt{d\mu/d\zeta} - \sqrt{d\nu/d\zeta})^2 \, d\zeta\big)^{1/2}$ between finite (in practice probability) measures, computed against any measure $\zeta$ dominating both, with the normalisation of Dashti and Stuart that puts the distance between probability measures in $[0, 1]$. It is the metric in which Bayesian posteriors are shown to depend continuously on the data and on approximations of the forward model, because it controls differences of expectations of functions with second moments.

- [Hellinger distance](hellinger-dist.md)
- [Hellinger distance through densities against any dominating measure](hellinger-dist-with-density.md)
- [The Hellinger distance is nonnegative](hellinger-dist-nonneg.md)
- [The Hellinger distance is symmetric](hellinger-dist-comm.md)
- [The Hellinger distance from a measure to itself is zero](hellinger-dist-self.md)
- [Hellinger is at most the square root of total variation](hellinger-dist-le-sqrt-total-variation-d.md)
- [Total variation is at most √2 times Hellinger](total-variation-dist-div-sqrt-two-le-hel.md)
- [The Hellinger distance between probability measures is at most one](hellinger-dist-le-one.md)
- [The Hellinger distance controls expectations](norm-integral-sub-integral-le-hellinger.md)

## Related topics

- [Total variation distance](../total-variation-distance/README.md): the other distance used for posterior stability; for probability measures $d_{\mathrm{TV}}/\sqrt2 \le d_{\mathrm{Hell}} \le d_{\mathrm{TV}}^{1/2}$ (Dashti and Stuart, Lemma 7.12).
- [Total variation and Pinsker's inequality](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/README.md): the comparison of total variation with the Kullback–Leibler divergence.
- [Bayesian inverse problems](../../bayesian-statistics/bayesian-inverse-problems/README.md): posteriors are Lipschitz in the data, and stable under approximation of the forward model, in the Hellinger distance.
