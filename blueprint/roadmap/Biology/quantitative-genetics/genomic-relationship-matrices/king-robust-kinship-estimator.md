# KING-robust kinship estimator

Let individuals $i$ and $j$ be genotyped at $M_{ij}$ biallelic SNPs (those non-missing in both), with genotypes coded as allele counts $x \in \{0, 1, 2\}$. Write $N_{Aa}^{(i)}$ and $N_{Aa}^{(j)}$ for the numbers of heterozygous SNPs of $i$ and of $j$, $N_{Aa,Aa}$ for the number of SNPs at which both are heterozygous, and $N_{AA,aa}$ for the number at which they carry opposite homozygotes. At every SNP,

$$(x_i - x_j)^2 = I_{Aa}(i) + I_{Aa}(j) - 2I_{Aa,Aa} + 4I_{AA,aa}.$$

Assume the two individuals are non-inbred, come from the same population, and are in Hardy–Weinberg proportions across SNPs sharing the same allele frequency. Estimating each individual's average heterozygosity $\mathbb E[2P(1-P)]$ by its observed heterozygosity rate, the **KING-robust** estimator of the kinship coefficient $\varphi_{ij}$ is

$$\hat\varphi_{ij} = \frac{N_{Aa,Aa} - 2N_{AA,aa}}{N_{Aa}^{(i)} + N_{Aa}^{(j)}},$$

a consistent estimator of $\varphi_{ij}$ that uses only the two individuals' genotypes. For between-family comparisons the heterozygosity is replaced by the smaller rate; if $N_{Aa}^{(i)} \le N_{Aa}^{(j)}$,

$$\hat\varphi_{ij}' = \frac12 - \frac{N_{Aa}^{(i)} + N_{Aa}^{(j)} - 2N_{Aa,Aa} + 4N_{AA,aa}}{4N_{Aa}^{(i)}} .$$

Both estimators are bounded above by $1/2$ and $\hat\varphi'_{ij} \le \hat\varphi_{ij}$. For unrelated individuals from different populations, $\hat\varphi_{ij}$ converges to a negative value, so strongly negative estimates flag population heterogeneity.

## Depends on

- [The KING moment](integral-sub-sq.md)
- [Kinship coefficient](kinship.md)

## Expansion

The genotype identity is checked on the six unordered genotype pairs. Summing over SNPs and taking expectations under the [KING moment](integral-sub-sq.md) with $F_i = F_j = 0$ gives $\sum (x_i - x_j)^2 \approx M_{ij}\, 2\mathbb E[2P(1-P)]\,(1 - 2\varphi_{ij})$. Replacing $M_{ij}\mathbb E[2P(1-P)]$ by $(N_{Aa}^{(i)} + N_{Aa}^{(j)})/2$ and solving for $\varphi_{ij}$ gives the first estimator; replacing it by $N_{Aa}^{(i)}$ gives the second, which guards against excess heterozygosity. Because no population allele frequencies enter, the estimate is invariant to the rest of the sample. Section 2.3, Equations (9) and (11).

## Sources

- A. Manichaikul, J. C. Mychaleckyj, S. S. Rich, K. Daly, M. Sale, W.-M. Chen, "Robust relationship inference in genome-wide association studies", Bioinformatics 26 (2010), 2867–2873, <https://doi.org/10.1093/bioinformatics/btq559> (PMC3025716).
