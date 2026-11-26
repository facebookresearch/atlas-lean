# Time-trend test for directional polygenic selection

**Score.** For a trait with genome-wide association results, choose $M$ approximately independent variants and weights $w_j$ (the effect sizes $\beta_j$, or only their signs), and form for each ancient individual $i$ the polygenic score

$$\mathrm{PGS}_i = \sum_{j=1}^{M} w_j\, G_{ij},$$

centred and scaled by the standard deviation of the score in present-day individuals.

**Model.** With sampling date $t_i$ (in units of $-10{,}000$ years), fit the linear mixed model

$$y_i = \alpha + \gamma\, t_i + g_i + e_i, \qquad \mathbf{g} \sim \mathcal{N}(\mathbf{0}, \sigma_g^2 K), \quad \mathbf{e} \sim \mathcal{N}(\mathbf{0}, \sigma_e^2 I),$$

where $y_i$ is the scaled score and $K$ is the genetic relationship matrix computed from independent SNPs. The coefficient $\gamma$ is the change of the score over ten millennia, in present-day standard deviations, and $\gamma \ne 0$ is evidence of directional selection on the combination of alleles the score tags.

**Sign-flip calibration.** To separate a polygenic trend from a few strongly selected variants, recompute the score many times with the same variants but independent random weights $\pm 1$; such scores should show no polygenic trend. Define the inflation factor

$$c = \frac{\operatorname{median}\, Z_\gamma^2 \text{ (random-sign scores)}}{0.455},$$

the ratio to the median of $\chi^2_1$, bounded between $1$ and a cap, and divide the observed $Z_\gamma^2$ by $c$.

A significant $\gamma$ shows that alleles which predict the trait today trended together in the past; it does not identify the phenotype that was the target of selection.

## Depends on

- [Logit-linear mixed-model test for directional selection](logit-linear-mixed-model-test-for-directional-selection.md)
- [Genetic relationship matrix entry](../../quantitative-genetics/genomic-relationship-matrices/grm.md)
- [Variance components of the linear mixed model](../../statistical-genetics/bolt-lmm-mixed-model-association/model.md)

## Expansion

If many variants each change frequency slightly in the direction that raises a trait, their weighted sum drifts steadily over time even when no single variant is detectable. The random effect removes the part of the score's variation explained by ancestry, which would otherwise create spurious trends whenever populations with different average scores replaced one another over time. Under random sign flips the polygenic signal cancels while structure, linkage and outlier variants remain, so the distribution of $Z_\gamma$ under flips measures the residual inflation that these other effects produce.

## Sources

- A. Akbari, A. Perry, A. R. Barton et al., "Ancient DNA reveals pervasive directional selection across West Eurasia", Nature (2026), Methods, "Polygenic score computation" (Eqs. 5–6), "Fitting the linear mixed model (LMM)" and "Adjusting for residual inflation in directional polygenic analysis", <https://doi.org/10.1038/s41586-026-10358-1>, PMCID PMC13189228.
