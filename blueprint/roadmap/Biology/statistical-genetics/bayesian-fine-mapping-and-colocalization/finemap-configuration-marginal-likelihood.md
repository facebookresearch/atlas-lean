# FINEMAP marginal likelihood and causal-subset Bayes factor

Let $\hat z \in \mathbb R^m$ be single-SNP $z$-scores and $R$ the $m \times m$ SNP correlation matrix of a region, from a sample of size $n$. A causal configuration is $\gamma \in \{0,1\}^m$ with $k = \sum_\ell \gamma_\ell$ causal SNPs, indexed by $C$, and $N$ the non-causal SNPs. Assume the summary-data likelihood $\hat z \mid \lambda \sim N(\sqrt n\, R \lambda, R)$ for standardized causal effects $\lambda$ (equivalent to $\hat\lambda \mid \lambda \sim N(\lambda, \sigma^2 (nR)^{-1})$ with $\sigma^2 = 1$), and the prior $\lambda \mid \gamma \sim N(0, s_\lambda^2 \Delta_\gamma)$ with $\Delta_\gamma = \operatorname{diag}(\gamma)$. Put $\Sigma_\gamma = n s_\lambda^2 \Delta_\gamma$. Then:

1. the marginal likelihood of $\gamma$ is $p(\hat z \mid \gamma) = N(\hat z \mid 0, R + R \Sigma_\gamma R)$;
2. if $R_{CC}$ is invertible, the Bayes factor against the null configuration depends only on the causal SNPs:

$$\mathrm{BF}(\gamma : \mathrm{NULL}) = \frac{N(\hat z \mid 0, R + R\Sigma_\gamma R)}{N(\hat z \mid 0, R)} = \frac{N\bigl(\hat z_C \mid 0, R_{CC} + n s_\lambda^2 R_{CC} R_{CC}\bigr)}{N(\hat z_C \mid 0, R_{CC})};$$

3. if $R$ is invertible and $a = R^{-1} \hat z$, then $\det(I_m + \Sigma_\gamma R) = \det(I_k + n s_\lambda^2 R_{CC})$, and the quadratic form $\hat z^\top (R + R\Sigma_\gamma R)^{-1} \hat z = \hat z^\top b$ where $b_N = a_N$ and $(I_k + n s_\lambda^2 R_{CC}) b_C = a_C - n s_\lambda^2 R_{CN} a_N$; evaluation costs $O(k^3)$ rather than $O(m^3)$.

With the prior $p(\gamma) = p_k / \binom{m}{k}$ for a distribution $(p_k)_{k=1}^{K}$ on the number of causal SNPs, the unnormalized posterior is $p_k \binom{m}{k}^{-1} \mathrm{BF}(\gamma : \mathrm{NULL})$.

## Expansion

(1) Integrate the Gaussian prior against the Gaussian likelihood: $\hat z = \sqrt n R\lambda + \text{noise}$ has covariance $n R \,\mathrm{Var}(\lambda) R + R = R\Sigma_\gamma R + R$. (2) Rows of $R\Sigma_\gamma$ vanish outside $C$, so in both numerator and denominator the conditional law of $\hat z_N$ given $\hat z_C$ is $N(R_{NC} R_{CC}^{-1} \hat z_C,\ R_{NN} - R_{NC} R_{CC}^{-1} R_{CN})$; these factors cancel. (3) $\Sigma_\gamma R$ has zero rows outside $C$, which gives the block structure of the linear system and of the determinant.

## Depends on

- [Wakefield approximate Bayes factor](wakefield-abf.md)

## Sources

- C. Benner, C. C. A. Spencer, A. S. Havulinna et al., "FINEMAP: efficient variable selection using summary data from genome-wide association studies", *Bioinformatics* 32 (2016), 1493–1501, <https://doi.org/10.1093/bioinformatics/btw018> (PMC4866522). Sections 2.1–2.4 (likelihood, priors, Options 1 and 2 for the marginal likelihood, posterior).
