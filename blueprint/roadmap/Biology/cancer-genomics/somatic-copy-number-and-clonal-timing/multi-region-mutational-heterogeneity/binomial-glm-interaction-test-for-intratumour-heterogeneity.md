# Binomial GLM interaction test for intratumour heterogeneity

With the read counts of the
[purity-adjusted heterogeneity index](purity-adjusted-heterogeneity-index-for-multi-region-sequencing.md),
model $X_{ij}$ as overdispersed binomial with $n_{ij}$ trials and success probability

$$\pi_{ij} = \operatorname{logit}^{-1}\!\big(\alpha_i + \beta_j + \gamma_{ij}\big), \qquad
E[X_{ij}] = n_{ij}\,\pi_{ij},$$

where $\alpha_i$ is the average frequency of gene $i$, $\beta_j$ is the common shift of all gene
frequencies in sample $j$ (from tumour cellularity), and $\gamma_{ij}$ is the deviation of gene $i$
in sample $j$ from that additive trend. With $g \cdot b$ observations and $g + b - 1$ identifiable
main-effect parameters, at most $(g-1)(b-1)$ interaction terms are identifiable. The tumour is
called heterogeneous by the likelihood ratio test of

$$H_0:\ \gamma_{ij} = 0 \text{ for all } i, j,$$

referred to a $\chi^2$ distribution with $(g-1)(b-1)$ degrees of freedom after scaling the deviance
by a fixed dispersion factor; a gene-specific test uses interaction terms for that gene only, and
$p$-values across tumours are corrected by the Benjamini–Hochberg procedure.

## Depends on

- [Purity-adjusted heterogeneity index for multi-region sequencing](purity-adjusted-heterogeneity-index-for-multi-region-sequencing.md)

## Expansion

On the logit scale, a change of tumour cellularity between samples shifts all mutations of a
sample together, which is absorbed by $\beta_j$; a clonal tumour sampled at different purities
therefore fits the main-effects model. Only a gene whose frequency moves differently from the
others, a mutation private to one region or subclonal in some regions, requires $\gamma_{ij} \ne 0$.
The interaction terms form a saturated model with $gb$ parameters, so the test compares the
additive model's deviance with zero, and its degrees of freedom are $gb - (g + b - 1) = (g-1)(b-1)$. Overdispersion from library preparation is handled with a quasibinomial family and a
fixed dispersion.

## Sources

- L. R. Yates, M. Gerstung, S. Knappskog, C. Desmedt, G. Gundem, P. Van Loo, T. Aas,
  L. B. Alexandrov, D. Larsimont, H. Davies, et al., "Subclonal diversification of primary breast
  cancer revealed by multiregion sequencing", Nature Medicine 21 (2015) 751-759, Online Methods,
  "Measuring heterogeneity in targeted capture data", part (iv), "Testing for heterogeneity",
  <https://doi.org/10.1038/nm.3886> (PMC4500826).
