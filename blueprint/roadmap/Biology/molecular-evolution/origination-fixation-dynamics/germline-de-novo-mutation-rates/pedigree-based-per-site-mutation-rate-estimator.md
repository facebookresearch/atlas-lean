# Pedigree-based per-site mutation rate estimator

**Setting.** A parent-offspring trio of a diploid species is sequenced, and a pipeline reports $n$ candidate de novo mutations (DNMs) in the offspring. Let $\mathrm{FDR}$ be the fraction of candidates that are false positives, $\mathrm{CG}$ the callable genome (the number of haploid sites at which a DNM would have been detectable after all site and individual filters), and $\mathrm{FNR}$ the fraction of true DNMs at callable sites that the remaining candidate filters miss.

**Estimator.** Assuming the per-site mutation rate is the same at callable and non-callable sites, the per-site per-generation mutation rate is estimated by

$$\hat\mu = \frac{n\,(1 - \mathrm{FDR})}{2 \cdot \mathrm{CG} \cdot (1 - \mathrm{FNR})}.$$

**Estimating the false-negative rate from an allelic-balance filter.** If candidates are required to have an allelic balance (alternate read fraction) inside an interval, a true DNM is missed whenever a true heterozygote's allelic balance falls outside it. Inherited sites that must be heterozygous in the offspring (one parent homozygous reference, the other homozygous alternate) give

$$\widehat{\mathrm{FNR}} = \frac{\#\{\text{true heterozygous sites outside the allelic-balance interval}\}}{\#\{\text{true heterozygous sites}\}}.$$

Alternatively, the effective callable site count $\mathrm{CG}\,(1 - \mathrm{FNR})$ can be computed site by site as $\sum_s \pi_s$, where $\pi_s$ is the probability that a DNM at genomic site $s$ would pass all filters given the depths there, which merges $\mathrm{CG}$ and $1 - \mathrm{FNR}$ into one term. The two transmitted copies of each site keep the factor $2$, so the denominator becomes $2\sum_s \pi_s$:

$$\hat\mu = \frac{n\,(1 - \mathrm{FDR})}{2\sum_s \pi_s}.$$

With perfect detection at $L$ callable sites, $\pi_s = 1$ and both forms divide by $2L$.

## Expansion

Each offspring genome is formed from two gametes, so a DNM can arise on either of $2\cdot\mathrm{CG}$ callable haploid positions. If each position mutates independently with probability $\mu$ and the pipeline detects a true DNM with probability $1 - \mathrm{FNR}$, the expected number of true detections is $2\,\mathrm{CG}\,\mu\,(1 - \mathrm{FNR})$; a fraction $1 - \mathrm{FDR}$ of the $n$ candidates are true, and equating the two gives $\hat\mu$. Different choices for $\mathrm{CG}$ (whole genome versus filtered sites) and for $\mathrm{FNR}$ can change $\hat\mu$ several-fold for the same trio, which is why each correction must be reported with the estimate.

## Sources

- L. A. Bergeron, S. Besenbacher, T. Turner, C. J. Versoza, R. J. Wang, A. L. Price, E. Armstrong, M. Riera, J. Carlson, H. Chen, M. W. Hahn, et al., *The Mutationathon highlights the importance of reaching standardization in estimates of pedigree-based germline mutation rates*, eLife 11 (2022), e73577, <https://doi.org/10.7554/eLife.73577>, PMCID PMC8830884. Results, "Step 5: Mutation rate estimation" (the estimator), "Callable genome" and "Assessing false-negatives" (allelic-balance FNR and site-wise detection probabilities).
