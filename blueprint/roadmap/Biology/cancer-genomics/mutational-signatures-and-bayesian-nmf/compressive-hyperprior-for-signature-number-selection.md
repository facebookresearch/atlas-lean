# Compressive hyperprior for signature-number selection

In [Poisson NMF](power-posterior-for-poisson-nmf.md) with $J$ samples and $K$ candidate signatures, place the hierarchical prior

$$R_k \sim \mathrm{Dirichlet}_I(\alpha_0, \dots, \alpha_0), \qquad L_{jk} \mid \mu_k \sim \mathrm{Gamma}(a,\, a/\mu_k), \qquad \mu_k \sim \mathrm{InvGamma}(a_0, b_0),$$

independently over $j$ and $k$, with shape $a > 0$, rate $a/\mu_k$ (so $\mathbb E[L_{jk} \mid \mu_k] = \mu_k$), and hyperparameters $a_0 = J_0 a + 1$, $b_0 = \varepsilon(a_0 - 1)$ for a pseudo-sample size $J_0 > 0$ and a small $\varepsilon > 0$.

**Proposition (compressive full conditional).** The prior mean of $\mu_k$ is $\varepsilon$, and given the loadings,

$$\mu_k \mid L \sim \mathrm{InvGamma}\Big(a_0 + J a,\; b_0 + a \sum_{j=1}^J L_{jk}\Big), \qquad \mathbb E[\mu_k \mid L, R, X, \mu_{-k}] = \frac{J_0}{J_0 + J}\, \varepsilon + \frac{J}{J_0 + J}\Big(\frac1J \sum_{j=1}^J L_{jk}\Big).$$

The conditional mean is a convex combination of the prior value $\varepsilon$ and the average loading of process $k$, with weight $J_0/(J_0 + J)$ on $\varepsilon$. For processes the data do not need, the posterior pulls $\mu_k$ down to about $\varepsilon$ and hence their loadings to negligible values, effectively removing them; active processes are shrunk only mildly. The number of active signatures (for instance those with $\mu_k$ above $2\varepsilon$) is therefore selected automatically, with $K$ only an upper bound.

## Depends on

- [Power posterior for Poisson NMF](power-posterior-for-poisson-nmf.md)
- [Dirichlet distribution](../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Proof sketch

As a function of $\mu_k$, the gamma density of $L_{jk}$ is proportional to $\mu_k^{-a} e^{-a L_{jk}/\mu_k}$, so the $J$ loadings multiply the inverse-gamma prior $\mu_k^{-a_0 - 1} e^{-b_0/\mu_k}$ into an inverse-gamma with shape $a_0 + Ja$ and scale $b_0 + a\sum_j L_{jk}$. Its mean is

$$\frac{b_0 + a\sum_j L_{jk}}{a_0 + Ja - 1} = \frac{\varepsilon J_0 a + a\sum_j L_{jk}}{a(J_0 + J)},$$

which is the displayed formula; the prior mean is $b_0/(a_0 - 1) = \varepsilon$. With $\alpha_0 = 1/2$ the Dirichlet prior is the Jeffreys prior for a multinomial, and with $a = 1/2$ the conditional variance of $L_{jk}$ is $\mu_k^2/a = 2\mu_k^2$. A fixed $J_0$ gives a fixed-strength prior, while $J_0 = J$ makes the penalty grow with the data and yields asymptotic sparsity as $J \to \infty$.

## Sources

- C. Xue, J. W. Miller, S. L. Carter and J. H. Huggins, "Robust discovery of mutational signatures using power posteriors", PLoS Computational Biology 22 (2026), e1014372, Methods ("Model and sparsity-inducing prior", Eqs. (3)–(5) and the full-conditional mean of $\mu_k$), <https://doi.org/10.1371/journal.pcbi.1014372>, PMCID PMC13274926.
