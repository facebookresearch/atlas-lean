# Total variation is at most √2 times Hellinger

For probability measures $\mu$ and $\nu$,

$$
\frac{1}{\sqrt 2} \, d_{\mathrm{TV}}(\mu, \nu) \le d_{\mathrm{Hell}}(\mu, \nu),
$$

with $d_{\mathrm{TV}}(\mu, \nu) = \sup_B |\mu(B) - \nu(B)|$. Dashti and Stuart factor
$|a - b| = |\sqrt a - \sqrt b|\,(\sqrt a + \sqrt b)$ and apply the Cauchy–Schwarz inequality; equivalently,
integrate the pointwise bound
$|\sqrt a - \sqrt b|(\sqrt a + \sqrt b) \le \tfrac t2 (\sqrt a - \sqrt b)^2 + \tfrac1{2t} (\sqrt a + \sqrt b)^2$ and
optimise over $t > 0$.

## Sources

- M. Dashti and A. M. Stuart, *The Bayesian Approach to Inverse Problems*, arXiv:1302.6989v4 (2015), in *Handbook of Uncertainty Quantification* (Springer, 2017), Lemma 7.12, first inequality.
