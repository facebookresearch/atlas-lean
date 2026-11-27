# Metropolis–Hastings acceptance probability for a prior-reversible proposal

For a posterior $\mu \propto e^{-\Phi} \mu_0$ and a proposal reversible for the prior $\mu_0$, the acceptance
probability is

$$
a(u, v) = \min\{1, \exp(\Phi(u) - \Phi(v))\} .
$$

Moves that decrease the potential are always accepted. No density with respect to Lebesgue measure
appears, which is why the formula makes sense in infinite dimensions.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Theorem 5.8 and Algorithm 5.10.
- Simon L. Cotter, Gareth O. Roberts, Andrew M. Stuart and David White, *MCMC methods for functions: modifying old algorithms to make them faster*, Statist. Sci. 28 (2013), no. 3, 424–446, DOI 10.1214/13-STS421; arXiv:1202.0709, Section 6.2.
