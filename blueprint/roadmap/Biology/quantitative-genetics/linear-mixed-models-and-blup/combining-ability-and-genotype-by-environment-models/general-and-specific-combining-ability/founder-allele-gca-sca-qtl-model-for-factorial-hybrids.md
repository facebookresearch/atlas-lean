# Founder-allele GCA–SCA QTL model for factorial hybrids

Let $N$ hybrids be produced by crossing recombinant lines derived from four founder lines of group D with recombinant lines derived from four founder lines of group F, each founder assumed to carry a distinct allele at every locus. At a marker, let $X_{FA_D} \in [0,1]^{N\times 4}$ and $X_{FA_F} \in [0,1]^{N\times 4}$ hold the probabilities that each hybrid received its D (respectively F) allele from each D (respectively F) founder, so each row sums to $1$, and let $X_{FA_{DF}} \in [0,1]^{N\times 16}$ be the matrix of all element-wise products of a column of $X_{FA_D}$ with a column of $X_{FA_F}$. The single-marker model for the vector $y$ of hybrid means is

$$y = \mathbf{1}\mu + A\alpha + B\beta + C(\alpha\beta) + X_{FA_D}\gamma_{FA_D} + X_{FA_F}\theta_{FA_F} + X_{FA_{DF}}(\gamma\theta)_{FA} + Z_D u_D + Z_F u_F + e,$$

where $A, B, C$ code fixed effects of the parental populations and their interactions, $u_D \sim \mathcal{N}(0, I\sigma_D^2)$ and $u_F \sim \mathcal{N}(0, I\sigma_F^2)$ are polygenic parental-line effects with incidence matrices $Z_D, Z_F$, and $e \sim \mathcal{N}(0, I\sigma_e^2)$. The founder main effects $\gamma_{FA_D} \in \mathbb{R}^4$ and $\theta_{FA_F} \in \mathbb{R}^4$ are the QTL contributions to GCA, and the $16$ interactions $(\gamma\theta)_{FA}$ are its contributions to SCA.

**Degrees of freedom.** Because each row of $X_{FA_D}$ and $X_{FA_F}$ sums to $1$, the QTL GCA effects carry $3$ degrees of freedom in each group and the SCA interactions $3 \times 3 = 9$, for $15$ in total; GCA and SCA QTL effects are tested by Wald tests on these contrasts.

## Remarks

Row sums equal to one make the columns of $X_{FA_D}$ collinear with the intercept, so only $4 - 1 = 3$ contrasts of $\gamma_{FA_D}$ are identifiable, and likewise for $\theta_{FA_F}$. The products satisfy $\sum_{b} (X_{FA_{DF}})_{\cdot,(a,b)} = (X_{FA_D})_{\cdot,a}$ and $\sum_a (X_{FA_{DF}})_{\cdot,(a,b)} = (X_{FA_F})_{\cdot,b}$, so the span of the $16$ interaction columns contains the main-effect columns; after removing them, an interaction table of size $4\times 4$ has $(4-1)(4-1) = 9$ free parameters, exactly as in a two-way ANOVA. Founder-allele probabilities at each marker are imputed from the parental lines' genotypes at flanking informative markers. Fixed population effects absorb the mean differences between biparental families so that QTL effects are estimated within families, and the random parental effects absorb background polygenic GCA for lines used in several hybrids.

## Depends on

- [GCA–SCA mixed model of hybrid values](gca-sca-mixed-model-of-hybrid-values.md)

## Sources

- H. Giraud, C. Bauland, M. Falque, et al., "Reciprocal Genetics: Identifying QTL for General and Specific Combining Abilities in Hybrids Between Multiparental Populations from Two Maize (*Zea mays* L.) Heterotic Groups", *Genetics* 207 (2017), section "QTL detection", Equation (2), <https://doi.org/10.1534/genetics.117.300305> (PMC5669627).
