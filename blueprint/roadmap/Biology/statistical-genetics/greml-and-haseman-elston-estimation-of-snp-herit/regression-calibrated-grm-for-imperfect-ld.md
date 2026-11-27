# Regression-calibrated relationship matrix for imperfect LD with causal variants

Let $G_{jk}$ be the genetic relationship between individuals $j, k$ at the (unobserved) causal variants and $A_{jk}$ the relationship estimated from $N$ genotyped SNPs (off-diagonal entries; on the diagonal use $G_{jj} - 1$ and $A_{jj} - 1$). Let $\beta = \mathrm{Cov}(G_{jk}, A_{jk}) / \mathrm{Var}(A_{jk})$ be the regression slope of $G$ on $A$ across pairs, and define the adjusted matrix

$$A^*_{jk} = \begin{cases} \beta A_{jk}, & j \ne k, \\ 1 + \beta (A_{jj} - 1), & j = k. \end{cases}$$

Suppose the trait follows $y = \mu \mathbf 1 + g + e$ with $\mathrm{Var}(y) = G \sigma_g^2 + I \sigma_e^2$, so that for $j \ne k$ the pairwise squared difference satisfies $E[(y_j - y_k)^2 \mid G] = 2\sigma_P^2 - 2\sigma_g^2 G_{jk}$ with $\sigma_P^2 = \sigma_g^2 + \sigma_e^2$. If $E(G_{jk} \mid A^*_{jk}) = A^*_{jk}$ (which holds when the regression of $G$ on $A$ is linear), then Assuming $G_{jj} = 1$ for every $j$ (no inbreeding at the causal variants), for $j \neq k$:

$$E[(y_j - y_k)^2 \mid A^*_{jk}] = 2\sigma_P^2 - 2\sigma_g^2 A^*_{jk},$$

so the Haseman–Elston slope of $(y_j - y_k)^2$ on $A^*_{jk}$ is still $-2\sigma_g^2$ and $\sigma_g^2$ is estimated without the attenuation caused by imperfect LD. Yang et al. found empirically that $\beta = 1 - (c + 1/N)/\mathrm{Var}(A_{jk})$, where $1/N$ is the sampling variance of $A_{jk}$ from $N$ SNPs and $c \ge 0$ depends on how much rarer the causal variants are than the SNPs ($c = 0$ when they share the SNP frequency spectrum).

## Expansion

By the tower property, $E[(y_j - y_k)^2 \mid A^*] = E\{E[(y_j - y_k)^2 \mid G] \mid A^*\} = 2\sigma_P^2 - 2\sigma_g^2 E(G_{jk} \mid A^*) = 2\sigma_P^2 - 2\sigma_g^2 A^*_{jk}$. Without calibration $E(G \mid A) = \beta A$ with $\beta < 1$, so regressing on $A$ estimates $\beta \sigma_g^2$. The empirical form of $\beta$ follows from the observation that $\mathrm{Cov}(G, A)$ did not depend on $N$ while $\mathrm{Var}(A)$ had an additive $1/N$ sampling term; the $c$ term is an empirical fit, not a derived result.

## Depends on

- [GREML covariance matrix](greml-cov.md)
- [Sampling variance of single-SNP genetic relationships](single-snp-relationship-sampling-variance.md)

## Sources

- J. Yang, B. Benyamin, B. P. McEvoy et al., "Common SNPs explain a large proportion of the heritability for human height", *Nature Genetics* 42 (2010), 565–569, <https://doi.org/10.1038/ng.608> (PMC3232052). Online Methods, equations [3] and [7]–[9] and the derivation of the regression of $\Delta y_{jk}^2$ on $A^*_{jk}$; Fig. 1 for the empirical fit of $c$.
