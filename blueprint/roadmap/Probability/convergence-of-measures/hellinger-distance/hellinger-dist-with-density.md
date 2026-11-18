# Hellinger distance through densities against any dominating measure

Let $\rho$ be a σ-finite measure and $f$, $g$ measurable densities, finite $\rho$-almost everywhere.
Then

$$
d_{\mathrm{Hell}}(\rho f, \rho g) = \sqrt{\frac12 \int \big(\sqrt{f} - \sqrt{g}\big)^2 \, d\rho},
$$

where $\rho f$ denotes the measure with density $f$ with respect to $\rho$. So the distance can be
computed against any common dominating measure: this is Dashti and Stuart's Definition 7.11, with
densities against a common reference measure. Their formula (7.22) is the special case of a
measure absolutely continuous with respect to the other, which serves as the reference measure. In the Bayesian setting the natural reference measure is the
prior, against which posteriors have explicit densities. The identity holds for every σ-finite
$\rho$, but it is meaningful only when $\rho f$ and $\rho g$ are finite measures.

The proof writes $f = (f + g)\, \tfrac{d\mu}{d\zeta}$ and $g = (f + g)\, \tfrac{d\nu}{d\zeta}$
$\rho$-almost everywhere, for $\zeta = \mu + \nu = \rho (f + g)$.

## Sources

- M. Dashti and A. M. Stuart, *The Bayesian Approach to Inverse Problems*, arXiv:1302.6989v4 (2015), in *Handbook of Uncertainty Quantification* (Springer, 2017), Section 7.2.4, Definition 7.11 (the distance is independent of the common reference measure)
  and formula (7.22).
