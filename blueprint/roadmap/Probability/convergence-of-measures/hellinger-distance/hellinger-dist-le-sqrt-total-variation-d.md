# Hellinger is at most the square root of total variation

For probability measures $\mu$ and $\nu$,

$$
d_{\mathrm{Hell}}(\mu, \nu) \le d_{\mathrm{TV}}(\mu, \nu)^{1/2},
$$

with $d_{\mathrm{TV}}(\mu, \nu) = \sup_B |\mu(B) - \nu(B)|$, which for probability measures equals Dashti
and Stuart's $\tfrac12 \int |d\mu/d\zeta - d\nu/d\zeta| \, d\zeta$. As in their proof, the pointwise bound
$(\sqrt a - \sqrt b)^2 \le |a - b|$ reduces the claim to $\tfrac12 \int |a - b| \, d\zeta \le d_{\mathrm{TV}}$,
obtained by splitting the integral along $\{a \le b\}$. Together with
[the reverse comparison](total-variation-dist-div-sqrt-two-le-hel.md) it shows that the two metrics
define the same topology.

## Sources

- M. Dashti and A. M. Stuart, *The Bayesian Approach to Inverse Problems*, arXiv:1302.6989v4 (2015), in *Handbook of Uncertainty Quantification* (Springer, 2017), Lemma 7.12, second inequality.
