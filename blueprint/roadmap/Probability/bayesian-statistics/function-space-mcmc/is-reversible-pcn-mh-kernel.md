# The pCN method is reversible for the posterior

Let $\mu_0$ be a centred Gaussian measure on a separable Banach space, $-1 \le \beta \le 1$ and $\Phi$
measurable. The pCN method (propose $v = \sqrt{1 - \beta^2}\, u + \beta \xi$ with $\xi \sim \mu_0$, accept with
probability $\min\{1, e^{\Phi(u) - \Phi(v)}\}$) satisfies detailed balance with respect to the posterior
$\mu \propto e^{-\Phi} \mu_0$, and hence leaves it invariant.

For example, the standard Gaussian prior on $\mathbb R$ with forward map $G(u) = u^3$, data $y = 1$ and potential $\Phi(u) = \tfrac12 (1 - u^3)^2$ satisfies the hypotheses.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Algorithm 5.10, from Example 5.3 and Theorem 5.8.
- Simon L. Cotter, Gareth O. Roberts, Andrew M. Stuart and David White, *MCMC methods for functions: modifying old algorithms to make them faster*, Statist. Sci. 28 (2013), no. 3, 424–446, DOI 10.1214/13-STS421; arXiv:1202.0709, Section 4.2 and Theorem 6.2.
