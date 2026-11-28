# Eigen-rotation of genomic kernel models

Let a training set of $n$ genotypes have phenotypes $y$ and a positive semidefinite relationship kernel $K$ (for example $K = ZZ^\top$), in the model

$$y = \mathbf 1\mu + g + e, \qquad g \sim N(0, K\sigma_g^2), \quad e \sim N(0, I\sigma_e^2). \tag{20}$$

Write the eigendecomposition $K = UD^2U^\top$ restricted to the positive eigenvalues, $Q = UD$ and $R = UD^{-1}$.

1. **Reparameterization.** $K = QQ^\top$, and (20) is equivalent to

$$y = \mathbf 1\mu + Q\alpha + e, \qquad \alpha \sim N(0, I\sigma_g^2), \tag{22}$$

since $\operatorname{Var}(Q\alpha) = QQ^\top\sigma_g^2 = K\sigma_g^2$; the model has independent effects and can be solved by coordinate-wise (Gauss–Seidel) updates. For $K = ZZ^\top$ with $p \gg n$ markers this reduces the number of effects from $p$ to at most $n$, and marker effects are recovered as $\beta = Z^\top R\alpha$.

2. **Prediction.** For new genotypes with cross-kernel $K_{\mathrm{PS},\mathrm{TS}}$ to the training set, set $Q_{\mathrm{PS}\mid\mathrm{TS}} = K_{\mathrm{PS},\mathrm{TS}}R$ and $\hat g_{\mathrm{PS}} = Q_{\mathrm{PS}\mid\mathrm{TS}}\hat\alpha$. On the training set itself $KR = Q$. If $K$ is nonsingular, then $\hat g_{\mathrm{PS}} = K_{\mathrm{PS},\mathrm{TS}}K^{-1}\hat g_{\mathrm{TS}}$ with $\hat g_{\mathrm{TS}} = Q\hat\alpha$, the usual BLUP extension to unobserved individuals.

3. **Diagonalization.** Regressing on eigenvectors instead, $y = \mathbf 1\mu + U\theta + e$ with $\theta \sim N(0, D^2\sigma_g^2)$, and premultiplying by $U^\top$ (when $U$ is square orthogonal) gives $U^\top y = U^\top\mathbf 1\mu + \theta + U^\top e$ with $\operatorname{Var}(U^\top e) = I\sigma_e^2$: the genetic effects become independent with heteroscedastic variances $d_i^2\sigma_g^2$.

## Depends on

- [BLUP is the conditional expectation](cond-exp-mixed-model.md)

## Expansion

$QQ^\top = UD^2U^\top = K$ and $KR = UD^2U^\top UD^{-1} = UD = Q$ use $U^\top U = I$. For part 2 with $K$ nonsingular, $\hat\alpha = Q^{-1}\hat g_{\mathrm{TS}} = D^{-1}U^\top\hat g_{\mathrm{TS}}$, so $Q_{\mathrm{PS}\mid\mathrm{TS}}\hat\alpha = K_{\mathrm{PS},\mathrm{TS}}UD^{-2}U^\top\hat g_{\mathrm{TS}} = K_{\mathrm{PS},\mathrm{TS}}K^{-1}\hat g_{\mathrm{TS}}$, which is the conditional mean of $g_{\mathrm{PS}}$ given $g_{\mathrm{TS}}$ under a joint Gaussian law with covariance kernel $K$. The same $U$ and $D$ come from the singular value decomposition $Z = UDV^\top$, which gives $Q = ZV$ and $\beta = V\alpha$.

## Sources

- A. Xavier, D. E. Runcie and D. Habier, *Megavariate methods capture complex genotype-by-environment interactions*, Genetics (2024), <https://doi.org/10.1093/genetics/iyae179>, PMCID PMC12005252 (Efficient parameterizations, equations (20)–(30)).
