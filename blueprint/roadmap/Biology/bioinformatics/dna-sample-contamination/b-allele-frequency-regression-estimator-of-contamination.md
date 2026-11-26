# B-allele-frequency regression estimator of contamination

**Setting.** A genotyping array reports, at each biallelic marker with arbitrarily labeled alleles $A$ and $B$, a called genotype $g \in \{AA, AB, BB\}$ and the B allele frequency (BAF), the normalized relative intensity of the $B$ probe, which is close to $0$, $1/2$ and $1$ for $AA$, $AB$ and $BB$ in a clean sample. Suppose a fraction $\alpha$ of the DNA comes from an unrelated contaminant whose two alleles at each marker are drawn independently of the target's genotype from population frequencies $p_A, p_B = 1 - p_A$, and that intensity is linear in DNA input.

**Conditional means.** At markers called homozygous in the target,

$$\mathbb{E}[\mathrm{BAF} \mid g = AA; \alpha, p_B] = \alpha\, p_B, \qquad \mathbb{E}[\mathrm{BAF} \mid g = BB; \alpha, p_A] = 1 - \alpha\, p_A.$$

**Regression estimator.** Over homozygous markers fit the linear model

$$\mathrm{BAF} = \gamma + \alpha\, p + \tau\, \mathbf{1}(g = AA) + \varepsilon, \qquad p = \begin{cases} p_B, & g = AA, \\ -p_A, & g = BB, \end{cases}$$

with intercept $\gamma$, genotype offset $\tau$ and Gaussian error $\varepsilon$. The least-squares slope $\hat\alpha$ estimates the contamination level, and the one-sided $t$-test of $\alpha = 0$ against $\alpha > 0$ tests for contamination.

**Minor-allele covariate.** When allele labels cannot be matched to nucleotides, only the minor allele frequency $f \in (0, 1/2]$ of a marker is known. Assume in addition that the label $B$ is attached to the minor allele with probability $1/2$, independently of the genotypes (exchangeable labels), and that the target's genotype follows [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md). Then $P(g = AA \mid B \text{ minor}) = (1-f)^2$ and $P(g = AA \mid A \text{ minor}) = f^2$, so by Bayes' rule $P(B \text{ minor} \mid g = AA) = (1-f)^2/((1-f)^2 + f^2)$ and

$$\mathbb{E}[\mathrm{BAF} \mid g = AA; \alpha, f] = \frac{\alpha f(1-f)}{(1-f)^2 + f^2}.$$

Without these assumptions the expression can fail: if $B$ is always the minor allele and $f = 1/4$, the conditional mean above is $\alpha p_B = \alpha/4$, not $3\alpha/10$. The expression is not linear in $f$; that the regression with covariate $f$ in place of $p$ gave nearly identical results to Equation 4 is an empirical observation of the source, not a property of the model.

## Expansion

At an $AA$ marker the contaminant contributes on average $p_B$ copies of $B$ per allele, so a fraction $\alpha$ of the intensity has $B$ share $p_B$; symmetrically at $BB$. Stacking both homozygous classes with the sign convention for $p$ makes the slope the same $\alpha$ in both, while $\gamma$ and $\tau$ absorb the two baseline BAF levels. The source fits the regression on markers called homozygous only; heterozygous markers are not used. The regression uses array data alone, so it can be run before sequencing.

## Depends on

- [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Proof depends on

- [Bayes' rule for discrete observations](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/posterior-eq-bayes-posterior.md)

## Sources

- G. Jun, M. Flickinger, K. N. Hetrick et al., "Detecting and estimating contamination of human DNA samples in sequencing and array-based genotype data", American Journal of Human Genetics 91 (2012), 839–848, Material and Methods, "Regression-Based Method" (Equation 4 and the minor-allele calculation following it), <https://doi.org/10.1016/j.ajhg.2012.09.004>, PMCID PMC3487130.
