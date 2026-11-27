# Purity-corrected integer copy number

Let a tumour sample be a mixture of malignant cells in proportion $\alpha \in (0, 1]$ (the purity) with diploid normal cells, let $\tau > 0$ be the average copy number of the malignant cells (their ploidy), and let $q(x) \in \mathbb{Z}_{\ge 0}$ be the integer copy number of the malignant cells at locus $x$. The observed copy ratio at $x$, normalized so that the genome-wide average is one, is

$$R(x) = \frac{\alpha q(x) + 2(1 - \alpha)}{D}, \qquad D = \alpha \tau + 2(1 - \alpha),$$

$D$ being the average copy number across all cells of the sample.

**Inversion.** For $\alpha > 0$ the map $q \mapsto R$ is affine and injective, so the malignant-cell copy number is recovered exactly from the observed ratio:

$$q(x) = \frac{D \, R(x)}{\alpha} - \frac{2(1 - \alpha)}{\alpha}.$$

**Corrected ratio.** Dividing by the malignant-cell ploidy gives the copy ratio as it would be observed in a pure tumour,

$$R'(x) = \frac{q(x)}{\tau} = \frac{D\,R(x) - 2(1 - \alpha)}{\alpha \tau},$$

an affine, strictly increasing function of $R(x)$ with slope $D/(\alpha\tau) = 1 + 2(1-\alpha)/(\alpha\tau) \ge 1$. Since $R(x) - 1 = (\alpha\tau/D)(R'(x) - 1)$, normal contamination acts on observed ratios as a contraction toward $1$ with factor $\alpha\tau/D$, and removing it in silico is the corresponding dilation by $D/(\alpha\tau)$. In the diploid-tumour case $\tau = 2$ (or when $\alpha = 1$), $D = \tau$ and this simplifies to $R'(x) = R(x)/\alpha - 2(1-\alpha)/(\alpha\tau)$ with contraction factor $\alpha$ (Zack et al. print this $\tau = 2$ form in general).

## Depends on

- [Average absolute copy number of a tumor sample](../../tumour-purity-ploidy-and-copy-ratio-algebra/mix-copy.md)
- [Relative copy ratio](../../tumour-purity-ploidy-and-copy-ratio-algebra/copy-ratio.md)

## Expansion

Both displayed identities are elementary rearrangements of the definition of $R$, valid whenever $\alpha > 0$ and $\tau > 0$. The practical content is in the scaling: when thresholds on copy ratio are applied to a cohort without correction, the effective threshold on the malignant-cell copy number varies from sample to sample through $\alpha$, so low-purity samples lose events at any fixed cut-off and the apparent rate of alterations is confounded with purity. Applying $R'$ before thresholding removes that confounding, at the cost of amplifying noise by the same factor $D/(\alpha\tau)$, which is why the correction is applied only to samples whose purity and ploidy could be called. The ploidy appearing in the denominator of $R'$ makes the corrected ratio invariant under a whole-genome doubling of the malignant cells, which multiplies both $q$ and $\tau$ by two.

## Sources

- T. I. Zack, S. E. Schumacher, S. L. Carter et al., "Pan-cancer patterns of somatic copy number alteration", Nature Genetics 45 (2013), 1134–1140, Methods section 5 ("Impurity-corrected GISTIC", the three displayed equations), <https://doi.org/10.1038/ng.2760>, PMCID PMC3966983.
- S. L. Carter, K. Cibulskis, E. Helman et al., "Absolute quantification of somatic DNA alterations in human cancer", Nature Biotechnology 30 (2012), 413–421, Eq. 1, <https://doi.org/10.1038/nbt.2203>.
