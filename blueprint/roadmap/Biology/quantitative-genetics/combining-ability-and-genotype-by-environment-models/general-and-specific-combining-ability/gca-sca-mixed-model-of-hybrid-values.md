# GCA–SCA mixed model of hybrid values

Consider single-cross hybrids $h = (k, k')$ between inbred line $k$ of group F and line $k'$ of group D, evaluated in environments $l$ with plot-level phenotypes $Y_{hl\cdot}$. The **GCA–SCA model** writes

$$Y_{hl\cdot} = \mu + \lambda_l + H_{h(kk')} + (\text{spatial effects}) + E_{hl\cdot}, \qquad H_{h(kk')} = u_{F,k} + u_{D,k'} + s_{kk'},$$

with fixed environment effects $\lambda_l$, and mutually independent random effects

$$u_{F,k} \sim \mathcal{N}(0, \sigma_F^2), \qquad u_{D,k'} \sim \mathcal{N}(0, \sigma_D^2), \qquad s_{kk'} \sim \mathcal{N}(0, \sigma_S^2), \qquad E_{hl\cdot} \sim \mathcal{N}(0, \sigma_{E_l}^2).$$

Here $u_{F,k}$ and $u_{D,k'}$ are the **general combining abilities** (GCA) of the two parents, with group-specific variances, and $s_{kk'}$ is the **specific combining ability** (SCA) of the pair. Consequently

$$\operatorname{Cov}\big(H_{(k,k')}, H_{(m,m')}\big) = \sigma_F^2\,[k = m] + \sigma_D^2\,[k' = m'] + \sigma_S^2\,[k = m,\ k' = m'],$$

so hybrids sharing one parent covary through that parent's GCA variance only, and the hybrid genetic variance is $\sigma_H^2 = \sigma_F^2 + \sigma_D^2 + \sigma_S^2$. The share of SCA, $\sigma_S^2/\sigma_H^2$, measures how much hybrid performance is not predictable from parental averages. With $\bar n$ the average number of plots per hybrid and $\bar\sigma_E^2$ the average residual variance, the design-level broad-sense heritability of hybrid means is $H = \sigma_H^2/(\sigma_H^2 + \bar\sigma_E^2/\bar n)$.

When parents come from structured families (e.g. biparental populations $ij$ in group F and $i'j'$ in group D), the model becomes

$$H_{h(kk')} = \alpha_{ij} + \beta_{i'j'} + (\alpha\beta)_{ij,i'j'} + u^{*}_{F,k} + u^{*}_{D,k'} + s^{*}_{kk'},$$

with fixed population and population-interaction effects and within-population GCA and SCA variances $\sigma_F^{*2}, \sigma_D^{*2}, \sigma_S^{*2}$.

## Remarks

The covariance formula follows by bilinearity from independence of the three random effects: $u_{F,k}$ is shared exactly when the F parents coincide, $u_{D,k'}$ when the D parents coincide, and $s_{kk'}$ only for the same pair. Under a biallelic additive–dominance model with loci in linkage equilibrium, the GCA of an F line is its expected hybrid value over random D partners (centred), which involves additive effects and the dominance deviations against the allele frequencies of the other group; the SCA collects the residual dominance (and epistatic) interaction between the two specific parental genotypes. Each variance component is estimated by REML, and the significance of $\sigma_F^2$, $\sigma_D^2$ or $\sigma_S^2$ is assessed by a likelihood-ratio test of the nested model with that component removed. In a sparse factorial design where most lines enter a single hybrid, GCA and SCA are only weakly separable, which trades variance-component precision for more distinct genotypes.

## Depends on

- [Marginal covariance of the mixed-model response](../../linear-mixed-models-and-blup/covariance-mixed-model-response.md)

## Sources

- H. Giraud, C. Bauland, M. Falque, et al., "Reciprocal Genetics: Identifying QTL for General and Specific Combining Abilities in Hybrids Between Multiparental Populations from Two Maize (*Zea mays* L.) Heterotic Groups", *Genetics* 207 (2017), section "Variance component analysis", Equations (1), (1.1) and (1.2), <https://doi.org/10.1534/genetics.117.300305> (PMC5669627).
