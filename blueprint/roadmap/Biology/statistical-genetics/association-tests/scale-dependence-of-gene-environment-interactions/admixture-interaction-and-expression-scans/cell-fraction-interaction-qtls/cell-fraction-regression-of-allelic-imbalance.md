# Cell-fraction regression of allelic imbalance

Fix a cis variant and a gene with a heterozygous, read-carrying (functional) site, phased so that reads can be assigned to the haplotype carrying the reference or alternative allele of the variant. Restrict to individuals heterozygous at the variant. For individual $i$ let $f_i\in[0,1]$ be the estimated fraction of a focal cell type, $D_i$ the total allele-assigned read depth and $\mathrm{ALT}_i$ the alternative-haplotype reads. Assume the population-level allelic fraction is a mixture

$$\pi(f)=\pi_f\,f+\pi_0\,(1-f)=\pi_0+(\pi_f-\pi_0)\,f,$$

with $\pi_f$ the allelic fraction in the focal cell type and $\pi_0$ that in all other cells, and model the reads as

$$\mathrm{ALT}_i\mid f_i\sim\mathrm{BetaBin}\bigl(D_i,\ \pi(f_i),\ \phi_i\bigr),$$

with overdispersion $\phi_i$ estimated per individual (per copy-number segment in tumors). Regressing $(\mathrm{REF}_i,\mathrm{ALT}_i)$ on $f_i$ with intercept $\mu_a$ and slope $\beta_f$:

1. $\mu_a\ne\tfrac12$ (on the probability scale at $f=0$, or for the population average) indicates population-level allelic imbalance;
2. the slope is zero, under the identity or the logit link, if and only if $\pi_f=\pi_0$, so a nonzero $\beta_f$ is a cell-fraction (cell-type-specific) allelic effect.

The analogous total-expression test is the interaction eQTL regression $y=\mu+\beta x+f+\beta_f\,x f$ over all genotypes $x\in\{0,1,2\}$. In tumors, a purity term is added to both models; a nonzero purity coefficient indicates a tumor-specific effect.

## Depends on

- [Beta-binomial mass function](../../../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/beta-binomial/beta-binomial-pmf.md): the read-count model

## Proof depends on

- [Variance of the beta-binomial law](../../../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/beta-binomial/variance-beta-binomial.md): the overdispersed variance

## Expansion

Linearity of $\pi$ in $f$ holds when the focal and other cells contribute reads of the gene in proportion to their abundance, that is, at equal per-cell expression. With per-cell expression levels $e_f$ and $e_0$ the read-weighted allelic fraction is $(\pi_f f e_f+\pi_0(1-f)e_0)/(f e_f+(1-f)e_0)$, still constant in $f$ exactly when $\pi_f=\pi_0$, so the null hypothesis of item 2 is unchanged though the alternative is no longer linear. Because any monotone link maps a constant function to a constant, the zero-slope null does not depend on the link. The beta-binomial allows $\operatorname{Var}\mathrm{ALT}_i=D_i\pi(1-\pi)[1+(D_i-1)\rho_i]$ with intra-class correlation $\rho_i$, absorbing the extra dispersion of RNA-seq allele counts and, in tumors, of copy-number-altered regions. Unlike single-sample imbalance tests, the regression tests a consistent trend across the heterozygous population, polarized to the variant allele.

## Sources

- C. A. Kalita and A. Gusev, "DeCAF: a novel method to identify cell-type specific regulatory variants and their role in cancer risk", Genome Biology 23 (2022), 152, Results (model description) and Methods ("Statistical model to detect cfQTLs", "Statistical model to account for tumor variation", "Simulation framework"), <https://doi.org/10.1186/s13059-022-02708-9> (PMC9264694).
