# Block-conditional likelihood of marginal association effects

**Setting.** Let the phenotype $Y \in \mathbb{R}^N$ and genotypes $X \in \mathbb{R}^{N \times M}$ be standardized (columns mean zero, variance one) and $Y = X\beta + \varepsilon$ with $\beta$ a random effect independent of $X$ and $\varepsilon$. The marginal effect estimates are $\hat\beta = X^{\top}Y/N$ and the sample LD matrix is $\hat D = X^{\top}X/N$. Partition SNPs into blocks (approximately independent LD blocks); for block $b$ write $\hat\beta_b$, $\hat D_b = X_b^{\top}X_b/N$, $\beta_b$, and let $h_b^2 = \sum_{i \in b} \sigma_i^2$ be the heritability carried by SNPs in $b$, where $\sigma_i^2 = \mathrm{Var}(\beta_i)$.

**Proposition.** Conditional on $\beta_b$ and $\hat D_b$, and treating the genotypes of SNPs outside $b$ as uncorrelated with $X_b$,

$$\mathbb{E}(\hat\beta_b \mid \beta_b, \hat D_b) = \hat D_b\, \beta_b, \qquad \mathrm{Var}(\hat\beta_b \mid \beta_b, \hat D_b) = \frac{1 - h_b^2}{N}\, \hat D_b,$$

and, asymptotically, $\hat\beta_b \mid \beta_b \sim \mathcal{N}\big(\hat D_b\beta_b,\ \tfrac{1 - h_b^2}{N}\hat D_b\big)$. For a prior $\prod_{i \in b} f(\beta_i)$, the block posterior is

$$f(\beta_b \mid \hat\beta_b, \hat D_b) \propto \mathcal{N}\!\Big(\hat\beta_b;\ \hat D_b\beta_b,\ \tfrac{1 - h_b^2}{N}\hat D_b\Big) \prod_{i \in b} f(\beta_i),$$

and a polygenic risk score is $\mathrm{PRS} = \sum_j X_j\, \mathbb{E}(\beta_j \mid \hat\beta, \hat D)$, with $\hat D$ replaced by a reference-panel LD matrix when individual genotypes are unavailable.

## Expansion

Write $\hat\beta_b = \frac1N X_b^{\top}(X_b\beta_b + X_{-b}\beta_{-b} + \varepsilon)$. The first term is $\hat D_b\beta_b$. The remainder $\frac1N X_b^{\top}(X_{-b}\beta_{-b} + \varepsilon)$ has mean zero, and since $X_{-b}\beta_{-b} + \varepsilon$ has per-individual variance $1 - h_b^2$ (the total phenotypic variance one minus what block $b$ explains), its covariance is $\frac{1}{N^2}X_b^{\top}(1 - h_b^2)I\,X_b = \frac{1 - h_b^2}{N}\hat D_b$. Working block by block avoids inverting the full, typically singular $M \times M$ LD matrix. When the prior is a mixture of a point mass and normals, each coordinate of $\beta_b$ given $\hat\beta_b$ and the other coordinates is again a two-component mixture, so the posterior mean can be approximated by Gibbs sampling. Using $1 - h_b^2$ instead of $1 - h_g^2$ (whole-genome SNP heritability) is the refinement that conditions on the block's own contribution.

## Sources

- Hu Y, Lu Q, Powles R, Yao X, Yang C, Fang F, Xu X, Zhao H, "Leveraging functional annotations in genetic risk prediction for human complex diseases" (2017), Methods, "Calculation of posterior effect sizes" and "Calculation of PRS", <https://doi.org/10.1371/journal.pcbi.1005589>, PMCID PMC5481142.
