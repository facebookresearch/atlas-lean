# Leave-one-out BLUP from a single model fit

Consider the linear mixed model $y = X\beta + Zb + \epsilon$ for a phenotype $y$ measured on $N$
individuals, with covariates $X$, a standardized $N \times M$ genotype matrix $Z$, random effects
$b \sim \mathcal{N}(0, (\sigma_g^2/M) I_M)$ and noise
$\epsilon \sim \mathcal{N}(0, \sigma_\epsilon^2 I_N)$, so that $y \sim \mathcal{N}(X\beta, V)$
with $V = \sigma_g^2 K + \sigma_\epsilon^2 I_N$ and $K = ZZ^{\mathsf T}/M$. Let
$\hat\sigma_g^2, \hat\sigma_\epsilon^2$ be REML estimates, $\tilde y = y - X\hat\beta$ the
residuals after covariates, and

$$y_{\mathrm{BLUP}} = \hat\sigma_g^2 K \hat V^{-1} \tilde y = H \tilde y,
\qquad H = \hat\sigma_g^2 K \hat V^{-1},$$

the in-sample best linear unbiased prediction. Then the leave-one-out cross-validated prediction
for individual $k$, obtained by refitting the predictor with $k$ removed, equals

$$y_{k,\,\mathrm{cvBLUP}} = \frac{y_{k,\,\mathrm{BLUP}} - H_{kk}\,\tilde y_k}{1 - H_{kk}},$$

so the whole collection of out-of-sample predictions follows from one fit, in time linear in $N$
once $H$ is available.

## Depends on

- [Linear mixed models and BLUP](../../quantitative-genetics/linear-mixed-models-and-blup/README.md)

## Expansion

The identity is the mixed-model analogue of the classical leave-one-out shortcut for linear
smoothers, where the deleted residual is the raw residual divided by $1 - H_{kk}$. Its use is
statistical rather than computational: the in-sample $y_{\mathrm{BLUP}}$ is correlated with the
noise $\epsilon$ of the same individual, so testing it against another phenotype measured in the
same samples produces false positives, whereas the cross-validated version is free of that
correlation. Applied to expression data with $Z$ restricted to variants cis to a gene, it gives a
predicted cis-genetic component per gene that can be tested against the expression of every distant
gene, replacing a variant-by-gene scan with a gene-by-gene one and reducing the number of
hypotheses by orders of magnitude.

## Sources

- X. Liu, J. A. Mefford, A. Dahl, Y. He, M. Subramaniam, A. Battle, A. L. Price, N. Zaitlen,
  "GBAT: a gene-based association test for robust detection of trans-gene regulation",
  Genome Biology 21 (2020) 211, Methods, Eq. (2),
  <https://doi.org/10.1186/s13059-020-02120-1> (PMC7444084).
