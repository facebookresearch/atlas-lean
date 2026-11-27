# REGENIE: stacked block ridge regression and LOCO association testing

**Model.** For $N$ individuals with trait $y$, covariates $X$ ($N\times C$, full rank) and standardized genotypes $G_S$ ($N\times M$), the infinitesimal whole-genome regression is

$$y = X\alpha + G_S\beta + \epsilon, \qquad \beta \sim \mathrm{MVN}(0,\sigma_g^2I_M), \qquad \epsilon \sim \mathrm{MVN}(0,\sigma_e^2I_N),$$

equivalently $y = X\alpha + g + \epsilon$ with $g \sim \mathrm{MVN}(0,\sigma_a^2K)$, $K = G_SG_S^\top/M$, $\sigma_a^2 = M\sigma_g^2$. Covariates are projected out with $P_X = I_N - X(X^\top X)^{-1}X^\top$: $\tilde y = P_Xy$, $\tilde G = P_XG_S$, both rescaled to unit variance.

**Step 1, level 0 (within blocks).** Split $\tilde G$ into blocks $\tilde G_i$ of consecutive SNPs. For a grid $\lambda \in \Lambda = \{\lambda_1,\dots,\lambda_R\}$, with $\lambda = M(1-h_g^2)/h_g^2$ for $R$ evenly spaced SNP-heritabilities $h_g^2 \in [0.01, 0.99]$, compute the ridge fits

$$\hat\gamma_\lambda = \arg\min_\gamma\{\|\tilde y - \tilde G_i\gamma\|_2^2 + \lambda\|\gamma\|_2^2\} = (\tilde G_i^\top\tilde G_i + \lambda I)^{-1}\tilde G_i^\top\tilde y,$$

the MAP estimate under $\gamma_j \overset{\text{iid}}{\sim} N(0,1/\lambda)$, and keep the block predictors $W_i = (\tilde G_i\hat\gamma_{\lambda_1},\dots,\tilde G_i\hat\gamma_{\lambda_R})$. Stack $W = (W_1,\dots,W_B)$, an $N \times BR$ matrix with $BR \ll M$.

**Step 1, level 1 (stacking).** With $W$ rescaled to unit-variance columns, fit $\hat\eta_\omega = (W^\top W + \omega I_{BR})^{-1}W^\top\tilde y$ for $\omega = BR(1-h_g^2)/h_g^2$ over a grid, choosing $\omega$ by $K$-fold cross-validation in which the level-0 predictors for each held-out fold are themselves fitted without that fold. Zeroing the entries of $\hat\eta$ for blocks on a chromosome gives the leave-one-chromosome-out (LOCO) polygenic prediction $\hat y^*_{\mathrm{LOCO}}$ for that chromosome.

**Step 2 (association).** For a variant $g$ with $\tilde g = P_Xg$ and $\tilde y_{\mathrm{resid,LOCO}} = \tilde y - \hat y^*_{\mathrm{LOCO}}$, fit $\tilde y_{\mathrm{resid,LOCO}} = \tilde g\beta + \tilde\epsilon$ and use the score statistic

$$T_{\mathrm{linear}} = \frac{\tilde g^\top\tilde y_{\mathrm{resid,LOCO}}}{\hat\sigma_e\,(\tilde g^\top\tilde g)^{1/2}}, \qquad \hat\sigma_e^2 = \frac{\|\tilde y_{\mathrm{resid,LOCO}}\|_2^2}{N-C},$$

compared with $N(0,1)$ (with $N-C\approx N$ in practice), treating the polygenic prediction as fixed. For binary traits, level 1 is a logistic ridge regression and Step 2 is a logistic score test with the LOCO prediction as an offset, with Firth-penalized likelihood ratio or saddle-point corrections for rare or unbalanced cases.

## Depends on

- [Proximal contamination](../proximal-contamination-in-mixed-model-associatio/mm-chi-sq-add-smul-vec-mul-vec.md)

## Expansion

Ridge regression on a block is the Gaussian-prior posterior mode, so a grid of $\lambda$ spans plausible per-block architectures; stacking learns how much of each block-level fit to trust. Removing the tested chromosome's blocks from the polygenic predictor avoids proximal contamination: if the tested SNP (or SNPs in LD with it) contributed to $\hat y^*$, the residual would absorb part of its effect and deflate the statistic.

## Sources

- Joelle S. Mbatchou, Leland Barnard and Joshua Backman, "Computationally efficient whole-genome regression for quantitative and binary traits", Nature Genetics (2021), <https://doi.org/10.1038/s41588-021-00870-7>. bioRxiv 10.1101/2020.06.19.162354. Methods, Eqs. (1)–(7); Supplementary Methods, Eqs. (11)–(25) and (27)–(34).
