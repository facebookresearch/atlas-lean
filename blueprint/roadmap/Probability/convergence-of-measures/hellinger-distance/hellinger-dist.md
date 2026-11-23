# Hellinger distance

For finite measures $\mu$ and $\nu$ on the same measurable space (in practice probability measures),
the Hellinger distance is

$$
d_{\mathrm{Hell}}(\mu, \nu) = \sqrt{\frac12 \int \Big(\sqrt{\tfrac{d\mu}{d\zeta}} - \sqrt{\tfrac{d\nu}{d\zeta}}\Big)^2 \, d\zeta}, \qquad \zeta = \mu + \nu .
$$

Any $\sigma$-finite measure $\rho$ with respect to which $\mu$ and $\nu$ have densities, measurable and
finite $\rho$-almost everywhere, gives the same value
([change of reference measure](hellinger-dist-with-density.md)), so the choice $\zeta = \mu + \nu$
only makes the definition free of choices. The factor $\tfrac12$ is the normalisation of Dashti and
Stuart, for which the distance between probability measures lies in $[0, 1]$.

The definition makes sense for any measures, but it is meaningful only for finite ones: for
infinite measures the integral can diverge, and the convention that a non-integrable function has
integral $0$ then gives a meaningless value (Lebesgue measure and twice Lebesgue measure on
$\mathbb R$ come out at distance $0$).

## Background

- [Total variation distance between finite measures](../total-variation-distance/total-variation-dist.md):
  the other metric on probability measures used for posterior stability; the two are compared in
  [Lemma 7.12](hellinger-dist-le-sqrt-total-variation-d.md).

## Sources

- M. Dashti and A. M. Stuart, *The Bayesian Approach to Inverse Problems*, arXiv:1302.6989v4 (2015), in *Handbook of Uncertainty Quantification* (Springer, 2017), Section 7.2.4, Definition 7.11.
