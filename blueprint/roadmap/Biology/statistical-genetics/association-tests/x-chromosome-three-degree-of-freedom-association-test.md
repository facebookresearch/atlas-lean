# Robust three-degree-of-freedom association test for an X-chromosomal SNP

For a bi-allelic X-chromosomal SNP with alleles $r, R$, individuals fall into five genotype groups: females $rr, rR, RR$ and males $r, R$. Code sex $S = 0$ for females and $S = 1$ for males. The additive covariate $G_A$ depends on the baseline allele and on the assumed X-inactivation (XCI) status; over the groups $(rr, rR, RR, r, R)$:

$$G_{A,R,I} = (0, \tfrac12, 1, 0, 1)^\top,\quad G_{A,r,I} = (1, \tfrac12, 0, 1, 0)^\top,\quad G_{A,R,N} = (0,1,2,0,1)^\top,\quad G_{A,r,N} = (2,1,0,1,0)^\top,$$

where $I$ assumes XCI and $N$ no XCI. Let $G_D$ indicate female heterozygotes and $G_S = G_A \times S$. For a binary or continuous trait $Y$ with link $g$ fit

$$g(E[Y]) = \beta_0 + \beta_S S + \beta_A G_A + \beta_D G_D + \beta_{GS} G_S$$

and test $H_0 : \beta_A = \beta_D = \beta_{GS} = 0$ with 3 degrees of freedom.

**Proposition.**

1. With $S$ in the model, the test of $\beta_A = 0$ in $g(E[Y]) = \beta_0 + \beta_S S + \beta_A G_A$ is the same for $G_{A,R,N}$ and $G_{A,r,N}$, since $G_{A,r,N} = 2\cdot\mathbf 1 - S - G_{A,R,N}$; without $S$, the two codings group the genotypes differently and give different tests. No such reparametrization links $G_{A,R,I}$ and $G_{A,r,N}$ in this model.
2. With $S$ and $G_S$ in the model, the test of $\beta_A = \beta_{GS} = 0$ is the same for every choice of baseline allele and XCI assumption.
3. The full 3 df test above is therefore invariant to the baseline allele and to the XCI assumption; the dominance term $G_D$ absorbs skewed XCI, which is statistically indistinguishable from a heterozygote effect different from $1/2$.
4. For noncentral $\chi^2$ statistics with a common noncentrality, the largest power loss of a 3 df test relative to a correctly specified 1 df test, over all noncentralities and significance levels, is about $18.8\%$ (at $\alpha \approx 0.0008$), and about $17.7\%$ at $\alpha = 5\times10^{-8}$.

## Depends on

- [Invariance of GLM association tests under block-triangular reparametrization of the design](invariance-of-glm-tests-under-block-triangular-reparametrization.md)

## Expansion

Parts 1 and 2 are applications of the block-triangular invariance theorem: in part 1 take secondary columns $(\mathbf 1, S)$, $T_{11} = I_2$, $T_{12} = (2, -1)^\top$, $T_{22} = -1$; in part 2 the secondary columns are again $(\mathbf 1, S)$ and the primary block $(G_A, G_S)$ of one coding is an invertible linear image of the other's primary block plus secondary columns, so the theorem applies. When $G_{A,R,I}$ and $G_{A,r,N}$ are compared without $G_S$, $X_2 = X_1T$ has no solution because the rank of $(X_1, X_2)$ exceeds that of $X_1$. Including $S$ also guards against confounding by sex, since sex is associated with X-chromosomal genotypes by construction. The power bound in part 4 depends only on the noncentrality and $\alpha$, so it holds for any 3 df versus correctly specified 1 df comparison.

## Sources

- B. Chen, R. V. Craiu, L. J. Strug and L. Sun, "The X factor: A robust and powerful approach to X-chromosome-inclusive whole-genome association studies", Genetic Epidemiology 45 (2021), 694, <https://doi.org/10.1002/gepi.22422> (PMC9292551). Section 2 (Equations 1–2, Table 2, Theorem 1 and its applications) and Section 3.1.
