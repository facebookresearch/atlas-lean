# Standardized annotation effect size $\tau^*$ in stratified LD-score regression

Consider [stratified LD-score regression](integral-chi-sq-of-annot.md) with real-valued (possibly continuous) annotations $a_c(j)$ and coefficients $\tau_c$, so that the per-SNP heritability of SNP $j$ is $\mathrm{Var}(\beta_j) = \sum_c a_c(j)\tau_c$ and

$$E[\chi^2_j] = N \sum_c \tau_c\, \ell(j, c) + N b + 1, \qquad \ell(j, c) = \sum_k a_c(k)\, r_{jk}^2,$$

with $b$ a confounding term. Let $M_{h^2}$ be the number of SNPs over which heritability is summed, $h_g^2 = \sum_{j=1}^{M_{h^2}} \sum_c a_c(j)\tau_c$ the SNP-heritability and $\mathrm{sd}_c$ the standard deviation of $a_c$ over those SNPs. The **per-standardized-annotation effect size** is

$$\tau_c^* = \frac{M_{h^2}\, \mathrm{sd}_c}{h_g^2}\, \tau_c,$$

the additive change in per-SNP heritability for a one-standard-deviation increase of $a_c$, holding the other annotations fixed, divided by the mean per-SNP heritability $h_g^2/M_{h^2}$. It is invariant under rescaling $a_c \mapsto \alpha a_c$ ($\alpha > 0$) of the annotation together with the compensating change of $\tau_c$, under shifts $a_c \mapsto a_c + \beta'$ when the model contains the all-ones base annotation, and under rescaling the trait, so it can be compared across annotations and traits. For a set $C$ of SNPs (e.g. a quintile of $a_c$) the model-implied heritability is $h_g^2(C) = \sum_{j \in C} \sum_{c'} a_{c'}(j)\tau_{c'}$.

## Expansion

The per-SNP heritability is linear in the annotations, so a change of $\mathrm{sd}_c$ in $a_c$ changes it by $\tau_c\,\mathrm{sd}_c$; dividing by $h_g^2/M_{h^2}$ gives $\tau_c^*$. Rescaling $a_c$ by $\alpha$ multiplies $\mathrm{sd}_c$ by $\alpha$ and divides the fitted $\tau_c$ by $\alpha$ (a shift changes only the coefficient of the all-ones base annotation), and scaling the trait multiplies all $\tau$ and $h_g^2$ by the same factor. Gazal et al. use $\tau^*$ to show that SNPs with low MAF-adjusted level of LD have larger per-SNP heritability (negative $\tau^*$ for the LLD annotation), a signature of negative selection.

## Depends on

- [Stratified LD-score regression](integral-chi-sq-of-annot.md)
- [Annotation LD score of a marker](annot-ldscore.md)

## Sources

- S. Gazal, H. K. Finucane, N. A. Furlotte et al., "Linkage disequilibrium-dependent architecture of human complex traits shows action of negative selection", *Nature Genetics* 49 (2017), 1421–1427, <https://doi.org/10.1038/ng.3954> (PMC6133304). Equations (1) and (6)–(8) and the quintile-heritability formula in the Online Methods, as numbered in the preprint version that was read.
