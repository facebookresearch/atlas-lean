# Multivariate normal model of LD-correlated association statistics

Consider $m$ standardized SNPs in a region, a quantitative phenotype $y \in \mathbb R^n$ with $y = \mu \mathbf 1 + \beta_c x_c + e$, $e \sim N(0, \sigma^2 I_n)$, and marginal association statistics $S_i = \sqrt n\, \hat\beta_i/\sigma$ with $\hat\beta_i = x_i^\top y/n$. Let $\Sigma$ be the $m \times m$ matrix of pairwise SNP correlations (linkage disequilibrium), $\Sigma_{ij} = x_i^\top x_j / n$.

1. **Single causal SNP.** For large $n$, $S_c$ is approximately $N(\lambda_c, 1)$ with noncentrality $\lambda_c = \sqrt n\, \beta_c/\sigma$, and $\operatorname{Cov}(S_i, S_j) = \Sigma_{ij}$. Hence for a pair of SNPs, $(S_i, S_j)^\top \sim N\bigl((\lambda_i, \lambda_j)^\top, \begin{pmatrix} 1 & r_{ij} \\ r_{ij} & 1 \end{pmatrix}\bigr)$, and if SNP $i$ is causal then $\lambda_j = r_{ij}\lambda_i$.

2. **Causal configurations.** Let $c \in \{-1, 0, 1\}^m$ record, for each SNP, a positive effect, no effect or a negative effect. With a common noncentrality $\lambda$ for all causal SNPs,

$$S \mid c \sim N(\lambda\, \Sigma c,\ \Sigma). \tag{1}$$

3. **Random effect sizes.** If instead the causal noncentralities are drawn as $\lambda_c \mid c \sim N(0, \Sigma_c)$ with $\Sigma_c$ diagonal, $(\Sigma_c)_{ii} = \sigma^2$ for causal SNPs and a small $\epsilon > 0$ otherwise, then the induced noncentrality is $\Sigma \lambda_c \sim N(0, \Sigma \Sigma_c \Sigma)$ and

$$S \mid c \sim N\bigl(0,\ \Sigma + \Sigma \Sigma_c \Sigma\bigr).$$

## Expansion

$\operatorname{Cov}(\sqrt n \hat\beta_i/\sigma, \sqrt n \hat\beta_j/\sigma) = x_i^\top \operatorname{Var}(y) x_j/(n\sigma^2) = \Sigma_{ij}$, and the mean of $\sqrt n \hat\beta_i/\sigma$ is $\sqrt n\, \beta_c \Sigma_{ic}/\sigma = \Sigma_{ic}\lambda_c$; summing over causal SNPs gives the mean $\Sigma \lambda_c$. Part 3 integrates the Gaussian mean in (1) against its Gaussian prior; $\epsilon$ keeps $\Sigma_c$ nonsingular.

## Sources

- F. Hormozdiari, E. Kostem, E. Y. Kang, B. Pasaniuc and E. Eskin, *Identifying causal variants at loci with multiple signals of association*, Genetics 198 (2014), 497–508, <https://doi.org/10.1534/genetics.114.167908>, PMCID PMC4196608 (Materials and Methods, equations (1) and (3)).
