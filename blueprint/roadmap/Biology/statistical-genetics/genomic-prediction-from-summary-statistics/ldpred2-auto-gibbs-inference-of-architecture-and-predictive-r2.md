# LDpred2-auto: Gibbs-sampler inference of heritability, polygenicity, selection parameter and predictive $r^2$

Let $M$ variants have genotype standard deviations $S_j > 0$, in-sample (or reference) correlation matrix $R \in \mathbb{R}^{M \times M}$, and let $\gamma_j$ be allele-scale effects with scaled effects $\beta_j = S_j \gamma_j$ (effects of standardized genotypes on a standardized phenotype). The **LDpred model** is the point-normal prior

$$\beta_j \sim \begin{cases} \mathcal{N}\big(0, \tfrac{h^2}{M p}\big) & \text{with probability } p, \\ 0 & \text{otherwise,} \end{cases}$$

with SNP heritability $h^2$ and polygenicity $p \in (0, 1]$. The **extended three-parameter model** lets expected effect size depend on allele frequency through a selection parameter $\alpha$:

$$\gamma_j \sim \begin{cases} \mathcal{N}\big(0, \sigma_\beta^2\, S_j^{2\alpha}\big) & \text{with probability } p, \\ 0 & \text{otherwise,} \end{cases}$$

which reduces to the LDpred model at $\alpha = -1$, $\sigma_\beta^2 = h^2/(Mp)$; $\alpha < 0$ gives larger allele-scale effects to rarer variants; estimates between $-1$ and $0$ are read as a signature of negative selection.

**Estimators.** LDpred2-auto runs a Gibbs sampler on $\beta$ given marginal summary statistics $\hat\beta$ and $R$, and within each iteration:
1. estimates the heritability as the variance of the current genetic predictor, $\hat h^2 = \beta^\top R \beta$ (local heritability of an LD block is $\beta_B^\top R_{BB} \beta_B$ restricted to the block);
2. draws $p \sim \mathrm{Beta}\big(1 + M_c/\bar{\ell}, \ 1 + (M - M_c)/\bar{\ell}\big)$, where $M_c = \#\{j : \beta_j \ne 0\}$ and $\bar\ell$ is the average LD score (the denominator shrinks the effective number of independent variants);
3. in the three-parameter model, re-estimates $(\alpha, \sigma_\beta^2)$ by maximizing the normal likelihood of the current nonzero $\gamma_j$ (resampled with replacement), with $\alpha$ bounded in $[-1.5, 0.5]$;
4. records per-variant posterior inclusion probabilities $\Pr(\beta_j \ne 0 \mid \text{data})$ as the frequency of $\beta_j \neq 0$.

**Predictive $r^2$ from two chains.** If $\beta^{(1)}$ and $\beta^{(2)}$ are draws from two independent chains (or from one chain far enough apart to be quasi-independent), then

$$\widehat{r^2} = \beta^{(1)\top} R\, \beta^{(2)}$$

is a draw for the out-of-sample squared correlation between the polygenic score with weights $\bar\beta = \mathbb{E}[\beta \mid \text{data}]$ and the phenotype in a target sample of the same ancestry. Its quantiles across iterations give a credible interval.

## Expansion

For a phenotype with genetic value $X\beta$ and standardized genotypes, $\operatorname{Var}(X\beta) = \beta^\top R \beta$, which motivates item 1. For item 2, given the indicators $\mathbb{1}[\beta_j \ne 0]$, a uniform prior on $p$ gives the Beta$(1 + M_c, 1 + M - M_c)$ posterior; dividing counts by $\bar\ell$ treats correlated variants as fewer effective trials. For the $r^2$ identity: the out-of-sample $r^2$ of a score with weights $\bar\beta$ is approximately $(\bar\beta^\top \hat\beta_{\text{test}})^2/(\bar\beta^\top R \bar\beta)$, where $\hat\beta_{\text{test}}$ are scaled marginal effects in the test sample. With two independent posterior draws, $\mathbb{E}[\beta^{(1)}] = \mathbb{E}[\beta^{(2)}] = \bar\beta$ and $\mathbb{E}[\beta^{(1)\top} R \beta^{(2)}] = \bar\beta^\top R \bar\beta$, while for a test sample of the same ancestry $\mathbb{E}[R\beta^{(2)}] \approx \hat\beta_{\text{test}}$; substituting gives $\beta^{(1)\top} R \beta^{(2)}$ as an estimate of $r^2$. At perfect prediction the two draws coincide and $\widehat{r^2} = \hat h^2$; with no power the draws are nearly uncorrelated and $\widehat{r^2} \approx 0$. In UK Biobank analyses of 248 phenotypes, most $\hat\alpha$ fall between $-1.0$ and $-0.3$ (mode $-0.65$) and most $\hat p$ between $0.001$ and $0.04$.

## Sources

- F. Privé, C. Albiñana, J. Arbel, B. Pasaniuc and B. J. Vilhjálmsson, "Inferring disease architecture and predictive ability with LDpred2-auto", The American Journal of Human Genetics 110 (2023), 2042–2055, Material and methods ("Optional extended model and inference with LDpred2-auto", Equations 1–2; "Inference of predictive performance $r^2$"), <https://doi.org/10.1016/j.ajhg.2023.10.010> (PMC10716363).
