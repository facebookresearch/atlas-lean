# SuSiE-RSS: fine-mapping from sufficient statistics and summary data

Let $y \in \mathbb{R}^N$ (centered) and $X \in \mathbb{R}^{N \times J}$ (column-centered genotypes) follow the multiple regression $y = X b + e$, $e \sim \mathcal{N}_N(0, \sigma^2 I_N)$, with the SuSiE prior on $b$. The likelihood is

$$\ell(b, \sigma^2; X, y) = (2\pi\sigma^2)^{-N/2} \exp\Big\{ -\frac{1}{2\sigma^2}\big( y^{\top} y - 2 b^{\top} X^{\top} y + b^{\top} X^{\top} X b \big) \Big\},$$

so $(X^{\top}X, X^{\top}y, y^{\top}y, N)$ are sufficient statistics. Writing $V_{xx} = X^{\top}X/N$, $v_{xy} = X^{\top}y/N$, $v_{yy} = y^{\top}y/N$,

$$\ell_{ss}(b, \sigma^2; V_{xx}, v_{xy}, v_{yy}, N) = (2\pi\sigma^2)^{-N/2} \exp\Big\{ -\frac{N}{2\sigma^2}\big( v_{yy} - 2 b^{\top} v_{xy} + b^{\top} V_{xx} b \big) \Big\}.$$

**Proposition (Zou et al. 2022).**
1. *(Exactness.)* The iterative Bayesian stepwise selection algorithm can be rewritten to use only sufficient statistics (IBSS-ss), and $\mathrm{IBSS}(X, y) = \mathrm{IBSS\text{-}ss}(X^{\top}X, X^{\top}y, y^{\top}y, N)$.
2. *(SuSiE-RSS.)* Replacing $V_{xx}$ by an estimate $\hat V_{xx}$ (e.g. from a reference panel) and running $\mathrm{IBSS\text{-}ss}(N \hat V_{xx}, X^{\top}y, y^{\top}y, N)$ is the same as fitting the SuSiE prior with the approximate likelihood $\ell_{\mathrm{RSS}}(b, \sigma^2) = \ell_{ss}(b, \sigma^2; \hat V_{xx}, v_{xy}, v_{yy}, N)$, which is exact when $\hat V_{xx} = V_{xx}$. With approximate LD the residual variance is fixed at $\sigma^2 = y^{\top}y/N$.
3. *(Standardized data.)* If $y^{\top}y = N$ and $x_j^{\top}x_j = N$ for all $j$, let $R$ be the in-sample LD (correlation) matrix, $\hat z_j$ the single-SNP $z$-scores (with residual variance estimated without degrees-of-freedom correction), and $\tilde z = D_z^{1/2} \hat z$ with $D_z = \operatorname{diag}\big(N/(N + \hat z_j^2)\big)$ the **PVE-adjusted $z$-scores**. Then

$$X^{\top}X = N R, \qquad X^{\top}y = \sqrt{N}\, \tilde z, \qquad y^{\top}y = N,$$

so $\ell(b, \sigma^2; X, y) = \ell_{ss}(b, \sigma^2; R, \tilde z/\sqrt N, 1, N)$, and with an out-of-sample estimate $\hat R \approx R$ the SuSiE-RSS likelihood is $\ell_{\mathrm{RSS}}(b) = \ell_{ss}(b, 1; \hat R, \tilde z / \sqrt N, 1, N)$.

## Depends on

- [Sum of Single Effects (SuSiE) model and factored variational family](../sum-of-single-effects-susie/sum-of-single-effects-model.md)
- [ELBO monotonicity and KL minimization of IBSS](../sum-of-single-effects-susie/ibss-elbo-monotonicity-and-kl-minimization.md)

## Expansion

Every quantity IBSS computes (single-effect regressions on residuals, expected residual sums of squares, the ELBO) is a function of $X^{\top}X$, $X^{\top}y$, $y^{\top}y$ and $N$; reorganizing the residual updates as $X^{\top}(y - X\bar b) = X^{\top}y - X^{\top}X\, \bar b$ gives IBSS-ss with $O(J^2)$ cost per iteration instead of $O(NJ)$. For standardized data the marginal slope of SNP $j$ is the sample correlation $r_j = x_j^{\top}y/N$, and with residual variance $1 - r_j^2$ its $z$-score is $\hat z_j = r_j\sqrt N / \sqrt{1 - r_j^2}$; solving gives $r_j^2 = \hat z_j^2 / (N + \hat z_j^2)$ and hence $x_j^{\top} y = \sqrt N\, \hat z_j \sqrt{N / (N + \hat z_j^2)}$, the PVE adjustment.

## Sources

- Y. Zou, P. Carbonetto, G. Wang and M. Stephens, "Fine-mapping from summary data with the 'Sum of Single Effects' model", PLoS Genetics 18 (2022), e1010299, section "SuSiE with summary data" (Eqs. 8–19), <https://doi.org/10.1371/journal.pgen.1010299> (PMC9337707).
