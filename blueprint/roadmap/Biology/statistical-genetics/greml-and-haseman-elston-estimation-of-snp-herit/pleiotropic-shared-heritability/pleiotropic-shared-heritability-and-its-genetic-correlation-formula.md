# Pleiotropic shared heritability and its genetic-correlation formula

Let $X$ be standardized genotypes at $m$ SNPs, and let $\beta_T, \beta_1, \dots, \beta_n \in \mathbb{R}^m$ be causal (standardized) SNP effects on a target disease $T$ and on $n$ auxiliary diseases, with genetic values $G_T = X\beta_T$ and $G_j = X\beta_j$. Write the target genetic value as a private part plus a pleiotropic part,

$$G_T = G_{\mathrm{private}} + \sum_{j=1}^{n} \alpha_j G_j .$$

The **pleiotropic shared heritability** is defined through the best weights,

$$\frac{h^2_{\mathrm{pleio}}}{h^2} = \max_{\alpha \in \mathbb{R}^n} r^2_{\mathrm{ind}}\Big(\sum_j \alpha_j G_j,\ G_T\Big),$$

the maximal squared correlation across individuals. Assume that effects of distinct SNPs in LD are uncorrelated, $\mathbb{E}[\beta_{T,i}\beta_{j,i'}\,\mathrm{LD}_{i,i'}] = 0$ for $i \ne i'$, and let the number of SNPs grow. Then:

1. The individual-level and SNP-level definitions agree: $r^2_{\mathrm{ind}}(\sum_j \alpha_j G_j, G_T) = r^2_{\mathrm{SNP}}(\sum_j \alpha_j \beta_j, \beta_T)$, the squared correlation of effect sizes across SNPs; in particular the quantity is the same on the liability and observed scales.
2. If $C_{DD}$ (the $n \times n$ per-SNP covariance matrix of the auxiliary effects) is invertible and $c_{TD}$ is the vector of per-SNP covariances with $\beta_T$, the optimal weights are $\alpha^* = C_{DD}^{-1} c_{TD}$ and $h^2_{\mathrm{pleio}} = m\, c_{TD}^\top C_{DD}^{-1} c_{TD}$.
3. In terms of the target heritability $h_T^2$, the vector $r_g[D,T]$ of genetic correlations between the auxiliary diseases and $T$, and the genetic correlation matrix $r_g[D,D]$ among the auxiliary diseases,

$$h^2_{\mathrm{pleio}} = h_T^2\; r_g[D,T]^\top\, r_g[D,D]^{-1}\, r_g[D,T], \qquad \frac{h^2_{\mathrm{pleio}}}{h^2} = r_g[D,T]^\top\, r_g[D,D]^{-1}\, r_g[D,T].$$

## Depends on

- [Bivariate LD-score model](../../genomic-prediction-from-summary-statistics/cross-trait-model.md): genetic covariance as the per-SNP covariance of effects ($\rho_g/M$), from which $c_{TD}$, $C_{DD}$ and the genetic correlations $r_g$ are formed
- [Random-effects model of LD-score regression](../../ld-score-regression/model.md): heritability as $M$ times the per-SNP effect variance
- [Standardized genotype matrix](../../ld-score-regression/is-standardized.md): the standardized genotypes $X$

## Proof depends on

- [Closed-form solution of the normal equations](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/normal-inv.md): the optimal weights $\alpha^* = C_{DD}^{-1} c_{TD}$

## Expansion

Under the no-correlated-effects-in-LD assumption the off-diagonal terms of $(X\beta_T)^\top X \beta_T = \sum_{i,i'} (X^\top X)_{ii'} \beta_{T,i}\beta_{T,i'}$ vanish in the limit, so covariances of genetic values reduce to inner products of effect vectors and correlations across individuals equal correlations across SNPs. Maximizing the squared correlation is equivalent to least squares regression of $\beta_T$ on $\beta_1, \dots, \beta_n$ across SNPs; setting the gradient of $\|\beta_T - \sum_j \alpha_j \beta_j\|^2$ to zero gives $C_{DD}\alpha^* = c_{TD}$, and the explained variance is $m\,\alpha^{*\top} C_{DD}\alpha^*$. Writing $c_{TD} = \operatorname{diag}(\sqrt{h_T^2/m}\,\sqrt{h_D^2/m})\, r_g[D,T]$ and $C_{DD}^{-1} = \operatorname{diag}(1/\sqrt{h_D^2/m})\, r_g[D,D]^{-1} \operatorname{diag}(1/\sqrt{h_D^2/m})$ makes the heritabilities of the auxiliary diseases cancel. The ratio is the population $R^2$ of a multiple regression and lies in $[0, 1]$; it depends on the chosen auxiliary set. Plugging in noisy genetic-correlation estimates biases it upward, so the paper applies a Monte Carlo bias correction; across common diseases roughly half of SNP heritability is shared with other traits.

## Sources

- Y. Zhao, B. Strober, K. Hou, G. Kerner, J. Danesh, S. Gazal, W. Cheng, M. Inouye, A. L. Price and X. Jiang, "Pleiotropic shared heritability quantifies the shared genetic variance of common diseases", *Nature Genetics* 58 (2026), 1248–1257, Methods "Definition of $h^2_{\mathrm{pleio}}$", Eqs. (4)–(26), <https://doi.org/10.1038/s41588-026-02607-w> (PMC13256260).
