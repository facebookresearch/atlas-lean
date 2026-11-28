# Covariate-adjusted LD score regression (cov-LDSC)

**Standard LDSC.** Let $x_1, \dots, x_N \in \mathbb{R}^M$ be standardized genotype vectors of $N$ individuals at $M$ SNPs and model phenotypes $y_i = x_i \beta + \epsilon_i$ with $\epsilon_1, \dots, \epsilon_N \overset{\mathrm{iid}}{\sim} N(0, \sigma_e^2)$ and random effects $\beta \in \mathbb{R}^M$ of mean zero and $\mathrm{var}(\beta_j) = h_g^2/M$. With $\chi_j^2 \approx (X_j^{\mathsf T} Y)^2/N$ the association statistic of SNP $j$, where $X_j = (x_{1j}, \dots, x_{Nj})^{\mathsf T}$ and $Y = (y_1, \dots, y_N)^{\mathsf T}$,

$$E[\chi_j^2] \approx 1 + Na + \frac{N h_g^2}{M}\, \ell(j), \qquad \ell(j) = \sum_k R_{jk}^2, \qquad (1)$$

where $a$ captures population structure and other confounding and $R_{jk}$ is the population correlation between SNPs $j$ and $k$. $h_g^2$ is estimated by weighted regression of $\chi_j^2$ on $\ell(j)$ with a block jackknife.

**Covariate adjustment.** Let $C$ be an $N \times K$ matrix of column-centred covariates with rows $c_i$ (for example genotype principal components) and $y_i = x_i\beta + c_i \beta_{\mathrm{cov}} + \epsilon_i$. Multiplying by $P = I - C(C^{\mathsf T} C)^{-1} C^{\mathsf T}$ gives

$$\tilde Y = \tilde X \beta + \tilde\epsilon, \qquad \tilde Y = PY,\ \tilde X = PX,\ \tilde\epsilon = P\epsilon, \qquad (2)$$

and Eq. (1) holds with both the association statistics and the LD scores computed from the covariate-adjusted genotypes $\tilde X$. cov-LDSC therefore computes **covariate-adjusted in-sample LD scores** from $\tilde X$ (or a random subsample of individuals) instead of taking LD scores from an external reference panel.

## Depends on

- [LD score of a marker](ld-score.md)
- [Random-effects model of LD-score regression](model.md)

## Expansion

$P$ is the orthogonal projection onto the complement of the column space of $C$; it removes the covariate term exactly ($PC = 0$), so Eq. (2) is again a linear polygenic model, now in projected genotypes, and the derivation of Eq. (1) goes through with LD computed from $\tilde X$. In a homogeneous population the adjusted LD is close to the unadjusted LD and a reference panel is adequate. In an admixed population, ancestry-correlated allele frequencies create long-range LD that the principal components partly remove, so neither unadjusted nor reference-panel LD matches $\tilde X$; in simulations unadjusted LDSC underestimated $h_g^2$ by 10–60% in admixed populations while cov-LDSC was accurate. Because LD scores are computed from genotyped SNPs, cov-LDSC targets the same estimand as GREML on genotyped SNPs rather than the common-variant heritability of reference-panel LDSC, and partitioned estimates are recommended only for annotations made of large contiguous regions such as gene sets.

## Sources

- Y. Luo, X. Li, X. Wang, S. Gazal, J. M. Mercader et al., "Estimating heritability and its enrichment in tissue-specific gene sets in admixed populations", Human Molecular Genetics 30(16) (2021), Materials and Methods ("Mathematical framework of cov-LDSC", Equations 1–2), <https://doi.org/10.1093/hmg/ddab130>, PMCID: PMC8330913.
