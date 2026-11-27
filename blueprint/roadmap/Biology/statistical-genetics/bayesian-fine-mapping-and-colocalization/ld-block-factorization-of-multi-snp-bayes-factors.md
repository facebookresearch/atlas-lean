# LD-block factorization of multi-SNP Bayes factors

Let $y$ and the columns of $G$ be centred, $\boldsymbol\beta \mid \boldsymbol\gamma \sim N(0, W)$ with $W$ diagonal (zero entries for SNPs outside the model), and let the residual precision $\tau$ be known (residual covariance $\tau^{-1} I$), so that $y \sim N(0, \tau^{-1} I + G W G^\top)$ under the model and $y \sim N(0, \tau^{-1} I)$ under the null. The Bayes factor of the multiple-regression model against the null is

$$\mathrm{BF}(\boldsymbol\beta; W) = \left|I + \tau G^\top G W\right|^{-1/2}\exp\!\left(\tfrac{\tau^2}{2}\, y^\top G\left[W(I + \tau G^\top G W)^{-1}\right]G^\top y\right).$$

**Factorization.** Partition the SNPs into non-overlapping LD blocks, $G = (G_{[1]},\dots,G_{[L]})$, $W = W_{[1]}\oplus\cdots\oplus W_{[L]}$, and replace $G^\top G$ by its block-diagonal part $G_{[1]}^\top G_{[1]}\oplus\cdots\oplus G_{[L]}^\top G_{[L]}$. Then

$$\mathrm{BF}(\boldsymbol\beta; W) = \prod_{k=1}^{L}\mathrm{BF}_{[k]}, \qquad \mathrm{BF}_{[k]} = \left|I + \tau G_{[k]}^\top G_{[k]} W_{[k]}\right|^{-1/2}\exp\!\left(\tfrac{\tau^2}{2}\, y^\top G_{[k]}\left[W_{[k]}(I + \tau G_{[k]}^\top G_{[k]} W_{[k]})^{-1}\right]G_{[k]}^\top y\right).$$

If, in addition, the prior on association indicators is independent across SNPs, the posterior over configurations factorizes approximately over blocks,

$$\Pr(\boldsymbol\gamma \mid y, G, \boldsymbol\alpha) \approx \prod_{k=1}^{L}\Pr(\boldsymbol\gamma_{[k]} \mid y, G, \boldsymbol\alpha),$$

so fine-mapping can be run on each block separately (with $\tau$ replaced by a block-wise point estimate via a Laplace approximation).

## Proof sketch

By the Woodbury identity, $(\tau^{-1} I + G W G^\top)^{-1} = \tau I - \tau^2 G W (I + \tau G^\top G W)^{-1} G^\top$, and by Sylvester's determinant identity $|I + \tau G W G^\top| = |I + \tau G^\top G W|$; the ratio of the two Gaussian densities is therefore the displayed Bayes factor, with the factor $\tau^2/2$ in the exponent. (Appendix D of the source prints $\tfrac12$; that is the special case of unit residual precision $\tau = 1$.) For example, with one centred unit-norm column $G$, $y = G$, $W = 1$ and $\tau = 2$, the variances along $G$ are $3/2$ and $1/2$ and the log density ratio's quadratic term is $\tfrac12 (2 - 2/3) = 2/3 = \tfrac{\tau^2}{2}\cdot\tfrac{1}{3}$. With block-diagonal $G^\top G$ and $W$, the matrix $I + \tau G^\top G W$ is block diagonal, so its determinant is the product of the block determinants and its inverse is the direct sum of the block inverses; the quadratic form then splits into a sum over blocks and the exponential into a product. The block-diagonal replacement is a denoised version of $G^\top G$: $G^\top G/n$ estimates the genotype covariance, which population-genetic theory predicts is strongly banded, and published genome segmentations into approximately independent LD blocks set the cross-block entries to zero. A posterior proportional to a product of block priors times block Bayes factors is a product of block posteriors.

## Depends on

- [Deterministic approximation of posteriors (DAP) for multi-SNP association](deterministic-approximation-of-posteriors-dap.md)

## Sources

- X. Wen, Y. Lee, F. Luca and R. Pique-Regi, "Efficient integrative multi-SNP association analysis via deterministic approximation of posteriors", American Journal of Human Genetics 98 (2016), 1114–1129, Equations 1–6 and Appendices A (Equation A1), B (Equations B1–B5) and D (Equations D1–D4), <https://doi.org/10.1016/j.ajhg.2016.03.029> (PMC4908152).
