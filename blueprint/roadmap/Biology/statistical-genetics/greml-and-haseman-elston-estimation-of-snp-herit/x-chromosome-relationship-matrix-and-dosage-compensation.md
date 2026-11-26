# X-chromosome relationship matrix and dosage compensation

Let $N$ X-chromosome SNPs have reference allele frequencies $p_i$, and let $x^M_{ij} \in \{0, 1\}$ and $x^F_{ij} \in \{0, 1, 2\}$ be the reference allele counts of male and female $j$. The X-chromosome relationship estimates are

$$\hat A^M_{jk} = \frac{1}{N} \sum_{i=1}^{N} \frac{(x^M_{ij} - p_i)(x^M_{ik} - p_i)}{p_i (1 - p_i)}, \qquad \hat A^F_{jk} = \frac{1}{N} \sum_{i=1}^{N} \frac{(x^F_{ij} - 2p_i)(x^F_{ik} - 2p_i)}{2 p_i (1 - p_i)},$$

$$\hat A^{MF}_{jk} = \frac{1}{N} \sum_{i=1}^{N} \frac{(x^M_{ij} - p_i)(x^F_{ik} - 2p_i)}{\sqrt{2}\, p_i (1 - p_i)},$$

for male–male, female–female and male–female pairs. With male–female genetic correlation $1$ and $\sigma_{X(M)} = d\, \sigma_{X(F)}$, the X-linked phenotypic covariances are

$$\operatorname{cov}_X(y^M_j, y^M_k) = d^2 A^M_{jk} \sigma^2_{X(F)}, \quad \operatorname{cov}_X(y^F_j, y^F_k) = A^F_{jk} \sigma^2_{X(F)}, \quad \operatorname{cov}_X(y^M_j, y^F_k) = d\, A^{MF}_{jk} \sigma^2_{X(F)}.$$

The lyonization coefficient is $d = 1$ for equal X-linked genetic variance in both sexes, $d = 1/\sqrt{2}$ with no dosage compensation (both female X chromosomes active), and $d = \sqrt{2}$ with full dosage compensation (one female X inactive). The single component $\sigma^2_{X(F)}$ is estimated by REML in $y = X\beta + g_X + g_G + \varepsilon$, conditional on the autosomal relationship matrix.

## Depends on

- [Partitioned GREML with several relationship matrices](partitioned-greml-with-several-relationship-matrices.md)

## Expansion

Each term standardizes genotypes by their variance under Hardy–Weinberg equilibrium: $p(1-p)$ for a hemizygous male, $2p(1-p)$ for a female, and the geometric mean $\sqrt{2}\, p(1-p)$ for a mixed pair. With full dosage compensation a male's single active X has the effect of two copies, doubling his X-linked variance relative to a female's, so $d^2 = 2$; with no compensation it is halved, so $d^2 = 1/2$.

## Sources

- J. Yang et al., *Genome partitioning of genetic variation for complex traits using common SNPs*, Nat. Genet. 43 (2011), 519–525. <https://doi.org/10.1038/ng.823> (PMCID: PMC4295936) Online Methods (variance attributable to the X chromosome).
