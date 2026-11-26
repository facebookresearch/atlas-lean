# Coloc posterior reweighting under alternative priors

Let $D$ be the summary data of two traits on a region and $\pi = (p_1, p_2, p_{12})$ the prior parameters of the colocalization model with regional hypotheses $H_0, \dots, H_4$. By Bayes' rule

$$P(H_i \mid D, \pi) \propto \mathrm{BF}_i \cdot P(H_i \mid \pi), \qquad \mathrm{BF}_i = \frac{P(D \mid H_i)}{P(D \mid H_0)},$$

and the Bayes factors do not depend on $\pi$.

**Proposition (prior sensitivity without refitting).** For any alternative prior $\pi^*$,

$$P(H_i \mid D, \pi^*) = \frac{P(H_i \mid D, \pi)\, P(H_i \mid \pi^*)/P(H_i \mid \pi)}{\sum_{j=0}^{4} P(H_j \mid D, \pi)\, P(H_j \mid \pi^*)/P(H_j \mid \pi)}.$$

A conclusion such as $P(H_4 \mid D, \pi) > 0.5$ is robust only if it holds over the plausible range of $p_{12}$; when it holds only for priors making $H_4$ at least as likely as $H_3$, the colocalization claim rests on the prior.

**Masking for multiple causal variants.** To relax the single-causal-variant assumption without a linkage-disequilibrium matrix aligned to study alleles, assume distinct causal variants of a trait are in linkage equilibrium: identify lead SNPs sequentially, at each step masking SNPs in LD with the leads already found. To colocalize a pair of lead SNPs, set the per-SNP Bayes factor to $1$ for every SNP-specific hypothesis involving a SNP in LD with any other lead SNP of that trait, then run the single-variant analysis.

## Depends on

- [Colocalization normalization identity](coloc-posterior-eq.md)
- [Bayes factor of a colocalization configuration](coloc-bf.md)

## Expansion

The identity is immediate: $P(H_i \mid D, \pi^*) \propto \mathrm{BF}_i P(H_i \mid \pi^*)$ and $\mathrm{BF}_i \propto P(H_i \mid D, \pi)/P(H_i \mid \pi)$. A full sensitivity analysis over a grid of $p_{12}$ values therefore costs one fit. Masking approximates stepwise conditioning when causal variants are independent; it multiplies the number of comparisons, but when causal variants are in LD with each other it often assigns posterior mass to $H_3$ when $H_4$ is true, so conditioning with an aligned LD matrix is preferred where available.

## Sources

- C. Wallace, "Eliciting priors and relaxing the single causal variant assumption in colocalisation analyses", *PLoS Genetics* 16 (2020), e1008720, <https://doi.org/10.1371/journal.pgen.1008720> (PMC7192519; sections "Sensitivity analysis" and "Conditioning and masking to allow for multiple causal variants").
