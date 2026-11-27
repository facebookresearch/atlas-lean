# Annotation-weighted burden, SKAT and ACAT-V statistics

For $n$ subjects with trait $Y_i$ (mean $\mu_i$), covariates $X_i$ and genotypes $G_i = (G_{i1}, \dots, G_{ip})$ of a set of $p$ rare variants, consider $g(\mu_i) = \alpha_0 + X_i^\top \alpha + G_i^\top \beta$ (with an additional random effect $b \sim N(0, \sum_l \theta_l \Phi_l)$ for related samples) and test $H_0 : \beta = 0$ with the marginal scores $S_j = \sum_i G_{ij}(Y_i - \hat\mu_i)$ computed under the null model. Model the effects as $\beta_j = c_j \gamma_j$ with latent causal indicator $c_j$, $\pi_j = \mathbb{E}[c_j]$ and $|\gamma_j| \propto w_j = \mathrm{Beta}(\mathrm{MAF}_j; a_1, a_2)$. For annotations $k = 0, \dots, K$ with values $A_{jk}$ across all $M$ sequenced variants, estimate

$$\hat\pi_{jk} = \frac{\operatorname{rank}(A_{jk})}{M}, \qquad \hat\pi_{j0} = 1,$$

so that a binary annotation gives $\hat\pi_{jk} \in \{0, 1\}$. The annotation-$k$ statistics are

$$Q_{\mathrm{Burden},k} = \Big(\sum_{j=1}^{p} \hat\pi_{jk} w_j S_j\Big)^2, \qquad Q_{\mathrm{SKAT},k} = \sum_{j=1}^{p} \hat\pi_{jk} w_j^2 S_j^2,$$

$$Q_{\mathrm{ACAT\text{-}V},k} = \overline{\hat\pi_{\cdot k} w^2 \mathrm{MAF}(1-\mathrm{MAF})}\, \tan\big((0.5 - p_{0,k})\pi\big) + \sum_{j=1}^{p'} \hat\pi_{jk} w_j^2 \mathrm{MAF}_j(1-\mathrm{MAF}_j) \tan\big((0.5 - p_j)\pi\big),$$

where the sum runs over the $p'$ variants with minor allele count above $10$, $p_j$ is the single-variant p-value of $S_j$, $p_{0,k}$ is the annotation-weighted burden p-value of the variants with minor allele count at most $10$, and the bar denotes the average of $\hat\pi_{jk} w_j^2 \mathrm{MAF}_j(1-\mathrm{MAF}_j)$ over those variants. Under $H_0$, $Q_{\mathrm{Burden},k}$ is asymptotically a scaled $\chi^2_1$, $Q_{\mathrm{SKAT},k}$ a mixture of $\chi^2_1$ variables, and $Q_{\mathrm{ACAT\text{-}V},k}$ approximately Cauchy, each accounting for linkage disequilibrium among the variants.

## Depends on

- [SKAT variance-component score statistic](../../skat-variance-component-test/skat-q.md)
- [Default SKAT variant weight from the Beta(1, 25) density](../../skat-variance-component-test/beta-weight.md)

## Expansion

Writing $\beta_j = (1 - \pi_j)\delta_0 + \pi_j \gamma_j$ makes each variant a point mass at zero with probability $1 - \pi_j$. The burden test assumes $\beta_j \propto \pi_j w_j$; the SKAT assumption $\mathbb{E}[\beta_j] = 0$, $\operatorname{Var}(\beta_j) = \pi_{jk} w_j^2 \tau_k$ yields the variance-component score statistic with weights $\pi_{jk} w_j^2$; ACAT-V multiplies each Cauchy-transformed single-variant p-value by the same factor. Weighting by MAF alone upweights the many non-causal rare variants of a whole-genome variant set, whereas annotation ranks (for example annotation principal components summarizing epigenetic, conservation or protein-function scores, transformed to the PHRED scale) concentrate the weight on variants likely to be functional. The intercept annotation $k = 0$ recovers the conventional MAF-weighted tests.

## Sources

- X. Li, Z. Li, H. Zhou et al., "Dynamic incorporation of multiple in silico functional annotations empowers rare variant association analysis of large whole-genome sequencing studies at scale", Nature Genetics 52 (2020), <https://doi.org/10.1038/s41588-020-0676-4> (PMC7483769). Online Methods.
