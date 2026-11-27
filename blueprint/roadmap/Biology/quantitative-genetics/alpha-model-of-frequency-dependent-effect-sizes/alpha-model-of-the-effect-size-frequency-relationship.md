# Alpha model of the effect-size–frequency relationship

Let a polygenic trait be $z = \sum_{l=1}^{L} \beta_l (g_{l,m} + g_{l,p}) + e$, with allelic effects $\beta_l$, maternal and paternal genotypes $g_{l,m}, g_{l,p} \in \{0, 1\}$ and environmental noise $e$, and let a causal variant have derived-allele frequency $x \in (0, 1)$. The **alpha model** posits

$$\mathbb{E}[\beta^2 \mid x] \;\propto\; \big(x(1 - x)\big)^{\alpha}$$

for a single parameter $\alpha \in \mathbb{R}$. Since a biallelic variant at Hardy–Weinberg equilibrium contributes additive variance $2x(1 - x)\beta^2$, the expected heritability contributed per variant is

$$\mathbb{E}[2x(1 - x)\beta^2 \mid x] \;\propto\; \big(x(1 - x)\big)^{1 + \alpha}.$$

Hence $\alpha = 0$ means effect sizes independent of frequency (common variants contribute more heritability), $\alpha = -1$ means every variant contributes the same expected heritability regardless of frequency, and $\alpha < 0$ means rare variants have larger effects, the signature expected under negative selection on trait-affecting alleles.

**Stabilizing selection produces $\alpha < 0$.** With Gaussian fitness $w(z) = \exp(-(M - z)^2 / (2V_S))$ centered at the population mean $M$, a causal allele with effect $\beta$ at frequency $x$ changes on average by

$$\mathbb{E}[\Delta x] \approx s_{ud}\, x(1 - x)(1 - 2x), \qquad s_{ud} = -\frac{\beta^2}{2V_S},$$

where $s_{ud}$ is the selection coefficient of the heterozygote for a rare allele (genotype fitnesses $w_k \approx 1 + s_{ud}(k - 2x)^2$ for $k$ copies). This is an underdominant form in which the minor allele is always disfavored and selection strength grows with $\beta^2$; large-effect alleles are thus kept at low frequency, giving a negative relationship between $\beta^2$ and $x(1-x)$. (Correction of the source: Koch and Sunyaev's Eq. (1) prints $\mathbb{E}[\Delta x] \approx s_{ud}\, x(1-x)(\tfrac12 - x)$ with the same $s_{ud}$, which is half the value derived from the stated model: $\bar w = 1 + 2s_{ud}\,x(1-x)$ and $\mathbb{E}[\Delta x] = \tfrac{x(1-x)}{2\bar w}\tfrac{d\bar w}{dx}$.)

## Depends on

- [Additive variance at a biallelic locus](../fisher-s-decomposition-of-genetic-variance/add-var-biallelic.md)
- [Gaussian stabilizing fitness](../continuum-of-alleles-model-of-mutation-and-stabi/fitness.md)
- [Directional selection, overdominance and underdominance at one locus](../../population-genetics/selection-migration-and-transmission/one-locus-selection-dynamics/one-locus-viability-selection-regimes.md)

## Expansion

The alpha model is a statistical summary rather than a population-genetic model: it fits only the mean of $\beta^2$ given frequency. Estimates across many human traits are consistently negative, roughly in $[-0.5, -0.2]$, which rules out fully neutral architectures and pleiotropic models in which selection on variants is unrelated to their effect on the focal trait. The fitted $\alpha$ depends both on the distribution of fitness effects of new mutations and on how effect sizes scale with selection: in simulations, with effect sizes $\mathbb{E}[\beta^2 \mid s] \propto s^{2\tau}$ (the model of Eyre-Walker), the estimate approaches $-2\tau$ as the distribution of fitness effects becomes highly leptokurtic. Different selection models (direct stabilizing selection, pleiotropic stabilizing selection, apparent stabilizing selection, directional selection) can produce similar $\alpha$ while implying different architectures, so $\alpha$ alone does not identify the mode of selection. The underdominant form arises because, with the population mean at the optimum, stabilizing selection acts on the variance the locus contributes, which is largest at $x = 1/2$, so selection always pushes the allele toward the nearer boundary.

## Sources

- E. M. Koch and S. R. Sunyaev, "Maintenance of complex trait variation: classic theory and modern data", *Frontiers in Genetics* 12 (2021), 763363, Eq. (1), Figures 1–2 and the section on alpha models, <https://doi.org/10.3389/fgene.2021.763363> (PMC8636146).
