# B-allele-frequency regression estimator of contamination

**Setting.** A genotyping array reports, at each biallelic marker with arbitrarily labeled alleles $A$ and $B$, a called genotype $g \in \{AA, AB, BB\}$ and the B allele frequency (BAF), the normalized relative intensity of the $B$ probe, which is close to $0$, $1/2$ and $1$ for $AA$, $AB$ and $BB$ in a clean sample. Suppose a fraction $\alpha$ of the DNA comes from an unrelated contaminant whose alleles are drawn from population frequencies $p_A, p_B = 1 - p_A$, and that intensity is linear in DNA input.

**Conditional means.** At markers called homozygous in the target,

$$\mathbb{E}[\mathrm{BAF} \mid g = AA; \alpha, p_B] = \alpha\, p_B, \qquad \mathbb{E}[\mathrm{BAF} \mid g = BB; \alpha, p_A] = 1 - \alpha\, p_A.$$

**Regression estimator.** Over homozygous markers fit the linear model

$$\mathrm{BAF} = \gamma + \alpha\, p + \tau\, \mathbf{1}(g = AA) + \varepsilon, \qquad p = \begin{cases} p_B, & g = AA, \\ -p_A, & g = BB, \end{cases}$$

with intercept $\gamma$, genotype offset $\tau$ and Gaussian error $\varepsilon$. The least-squares slope $\hat\alpha$ estimates the contamination level, and the one-sided $t$-test of $\alpha = 0$ against $\alpha > 0$ tests for contamination. When allele labels cannot be matched to nucleotides, the minor allele frequency $f$ can replace $p$; then $\mathbb{E}[\mathrm{BAF} \mid g = AA] = \alpha f(1-f)/((1-f)^2 + f^2)$, which is not linear in $f$, but the regression with covariate $f$ gave nearly identical estimates in the source's data.

## Expansion

At an $AA$ marker the contaminant contributes on average $p_B$ copies of $B$ per allele, so a fraction $\alpha$ of the intensity has $B$ share $p_B$; symmetrically at $BB$. Stacking both homozygous classes with the sign convention for $p$ makes the slope the same $\alpha$ in both, while $\gamma$ and $\tau$ absorb the two baseline BAF levels. Heterozygous markers are excluded because their BAF is much noisier and dilutes the slope. Unlike the intensity mixture likelihood, the regression gives a calibrated $p$-value with a few hundred homozygous markers, and it can be run before sequencing.

## Depends on

- [Read-mixture likelihood for the contamination fraction](read-mixture-likelihood-for-the-contamination-fraction.md)

## Sources

- G. Jun, M. Flickinger, K. N. Hetrick et al., "Detecting and estimating contamination of human DNA samples in sequencing and array-based genotype data", American Journal of Human Genetics 91 (2012), 839–848, Material and Methods, "Regression-Based Method" (Equation 4), <https://doi.org/10.1016/j.ajhg.2012.09.004>, PMCID PMC3487130.
