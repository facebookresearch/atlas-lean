# PRS-CSx: coupled continuous shrinkage prior for cross-population polygenic prediction

For populations $k = 1,\dots,K$ with $N_k$ individuals, standardized phenotypes $y_k$ and standardized genotypes $X_k$ ($N_k\times M_k$, columns of mean $0$ and variance $1$), assume

$$y_k = X_k\beta_k + \epsilon_k, \qquad \epsilon_k \sim \mathrm{MVN}(0, \sigma_k^2 I), \qquad p(\sigma_k^2) \propto \sigma_k^{-2}.$$

For each SNP $j$, the population-specific effects share a global–local scale mixture of normals:

$$\beta_{jk} \mid \psi_j, \sigma_k^2 \sim N\Big(0, \frac{\sigma_k^2}{N_k}\psi_j\Big), \qquad \psi_j \sim \mathrm{Gamma}(a, \delta_j), \qquad \delta_j \sim \mathrm{Gamma}(b, \phi),$$

independently over $j$, with the *same* local scale $\psi_j$ in every population where SNP $j$ is present, and a global shrinkage parameter $\phi$ shared by all SNPs. The paper uses the Strawderman–Berger choice $a = 1$, $b = 1/2$, under which the marginal prior of $\beta_{jk}$ has a spike of mass near $0$ and Cauchy-like tails.

Given marginal summary statistics $\hat\beta_k = X_k^\top y_k/N_k$ and an ancestry-matched LD matrix $D_k \approx X_k^\top X_k/N_k$, the likelihood depends on the data only through $(\hat\beta_k, D_k)$, and the posterior is sampled by a Gibbs sampler with block updates of $\beta_k$. For fixed $\phi$ the posterior means give one score per discovery population; the final predictor is a linear combination of these standardized scores, with $\phi$ and weights tuned on validation data.

## Expansion

Conditionally on $(\psi, \sigma_k^2)$ the model is Gaussian: using $X_k^\top X_k = N_kD_k$ and $X_k^\top y_k = N_k\hat\beta_k$, the posterior precision of $\beta_k$ is $(N_k/\sigma_k^2)(D_k + \Psi^{-1})$ with $\Psi = \operatorname{diag}(\psi_j)$, so

$$\beta_k \mid \cdot \sim N\Big((D_k + \Psi^{-1})^{-1}\hat\beta_k,\ \tfrac{\sigma_k^2}{N_k}(D_k + \Psi^{-1})^{-1}\Big).$$

The shared $\psi_j$ couples populations: its full conditional is generalized inverse Gaussian and depends on $\sum_k N_k\beta_{jk}^2/\sigma_k^2$, so a SNP with a strong signal in a large discovery sample is shrunk less in a small one, while effect sizes remain population specific.

## Sources

- Yunfeng Ruan, Kuang Lin and Yen‐Chen Anne Feng, "Improving polygenic prediction in ancestrally diverse populations", Nature Genetics (2022), <https://doi.org/10.1038/s41588-022-01054-7> (PMC9117455). Methods, "PRS-CSx" (model of PRS-CS: T. Ge et al., Nat. Commun. 2019).
