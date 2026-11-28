# Adaptive proportion from a full distribution of fitness effects

Work in the [full-DFE model of polymorphism and divergence counts](full-dfe-model-of-polymorphism-and-divergence-counts.md), with DFE $\varphi$ of the scaled selection coefficient $S$ and expected divergence $\mathbb{E}[D_{\mathrm{sel}} \mid \lambda, S] = \lambda S/(1 - e^{-S})$. The proportion $\alpha$ of substitutions at selected sites that are adaptive is the share of the expected selected divergence contributed by $S > 0$.

**From polymorphism data alone.** If $\varphi$ is estimated without divergence data, $\lambda$ cancels and

$$\alpha \approx \frac{\displaystyle\int_0^\infty \frac{S}{1 - e^{-S}}\, \varphi(S)\, dS}{\displaystyle\int_{-\infty}^\infty \frac{S}{1 - e^{-S}}\, \varphi(S)\, dS}.$$

**With divergence data.** Given observed divergence counts $d_{\mathrm{sel}}, d_{\mathrm{neut}}$ on $l^d_{\mathrm{sel}}, l^d_{\mathrm{neut}}$ sites and a deleterious DFE fitted to polymorphism data, the classical estimator subtracts the expected non-adaptive substitutions:

$$\alpha \approx \frac{d_{\mathrm{sel}} - \dfrac{l^d_{\mathrm{sel}}}{l^d_{\mathrm{neut}}}\, d_{\mathrm{neut}} \displaystyle\int_{-\infty}^0 \frac{S}{1 - e^{-S}}\, \varphi(S)\, dS}{d_{\mathrm{sel}}},$$

after first removing from $d_{\mathrm{sel}}$ and $d_{\mathrm{neut}}$ the expected number of ingroup polymorphisms counted as fixed differences (the divergence expectations at $\lambda = 0$). This version assumes the ingroup and outgroup lineages share the same scaled DFE; the polymorphism-only version does not.

## Remarks

Each new mutation with coefficient $S$ fixes at rate proportional to $S/(1 - e^{-S})$ relative to a neutral mutation, so the expected number of substitutions contributed by each part of the DFE is its weight times this factor. Splitting the integral at $S = 0$ separates adaptive from neutral and slightly deleterious substitutions. In the divergence-based version the neutral divergence calibrates $\lambda$, and the deleterious integral predicts how many selected-site substitutions would occur without adaptation; the excess is attributed to positive selection, as in the McDonald–Kreitman logic. Fitting a deleterious-only DFE to data that contain beneficial polymorphisms biases this subtraction. In simulations the polymorphism-only estimate recovered $\alpha$ accurately even when the individual parameters $p_b$ and $S_b$ were poorly identified, because $\alpha$ depends mainly on their product.

## Depends on

- [Full-DFE model of polymorphism and divergence counts](full-dfe-model-of-polymorphism-and-divergence-counts.md)

## Sources

- P. Tataru, M. Mollion, S. Glémin et al., "Inference of distribution of fitness effects and proportion of adaptive substitutions from polymorphism data", Genetics 207 (2017), <https://doi.org/10.1534/genetics.117.300323>, PMCID PMC5676230. Equations 8–10.
- A. Eyre-Walker and P. D. Keightley, "Estimating the rate of adaptive molecular evolution in the presence of slightly deleterious mutations and population size change", Molecular Biology and Evolution 26 (2009), <https://doi.org/10.1093/molbev/msp119>.
