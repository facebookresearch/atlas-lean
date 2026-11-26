# Pseudo-expectation Gauss–Seidel solver for SNP-BLUP

Consider the SNP-BLUP (ridge regression) model

$$y = \mathbf 1\mu + Z\beta + e, \qquad \beta \sim N(0, I\sigma_\beta^2), \quad e \sim N(0, I\sigma_e^2), \tag{31}$$

with $y \in \mathbb R^n$, allele-dosage columns $z_1, \dots, z_p$ of $Z$, and $\lambda = \sigma_e^2/\sigma_\beta^2$. For fixed variance components the BLUP of $(\mu, \beta)$ minimizes $Q(\mu, \beta) = \|y - \mathbf 1\mu - Z\beta\|^2 + \lambda\|\beta\|^2$.

**Gauss–Seidel with residual updating.** Keep the residual $\hat e = y - \mathbf 1\hat\mu - Z\hat\beta$. For each marker $j$ (in random order within a sweep),

$$\hat\beta_j^{\mathrm{new}} = \frac{z_j^\top \hat e + \hat\beta_j z_j^\top z_j}{z_j^\top z_j + \lambda}, \qquad \hat e \leftarrow \hat e - z_j\bigl(\hat\beta_j^{\mathrm{new}} - \hat\beta_j\bigr), \tag{34, 35}$$

and for the intercept $\hat\mu^{\mathrm{new}} = \hat\mu + n^{-1}\mathbf 1^\top\hat e$, $\hat e \leftarrow \hat e - \mathbf 1(\hat\mu^{\mathrm{new}} - \hat\mu)$. Each update is the exact minimizer of $Q$ in that coordinate with the others fixed, so $Q$ decreases monotonically along the sweeps, and since $Q$ is strictly convex in $(\mu, \beta)$ for $\lambda > 0$, the iterates converge to the BLUP.

**Pseudo-expectation variance components.** Between sweeps, the variance components are re-estimated by

$$\hat\sigma_\beta^2 = \frac{\tilde\beta^\top \hat\beta}{\operatorname{tr}(Z^\top S Z)}, \qquad \hat\sigma_e^2 = \frac{y^\top \hat e}{n - 1}, \tag{32, 33}$$

where $S = I - X(X^\top X)^{-1}X^\top$ absorbs the fixed effects and $\tilde\beta = Z^\top S y$; with the intercept as the only fixed effect, $\tilde\beta = Z^\top(y - \bar y\mathbf 1)$ and $\operatorname{tr}(Z^\top S Z) = \sum_j \sum_i (z_{ij} - \bar z_j)^2$. This pseudo-expectation estimator approximates REML. The solver extends to multivariate (multi-environment) models by updating, at each marker, the vector of environment-specific effects with the corresponding $K \times K$ system.

## Depends on

- [BLUP is the conditional expectation](cond-exp-mixed-model.md)

## Expansion

Holding all but $\beta_j$ fixed, $Q$ is the quadratic $\|r_j - z_j\beta_j\|^2 + \lambda\beta_j^2 + \text{const}$ with partial residual $r_j = \hat e + z_j\hat\beta_j$; its minimizer is $z_j^\top r_j/(z_j^\top z_j + \lambda)$, which is (34). The intercept step is the same with $z = \mathbf 1$ and no penalty. Coordinate descent on a strictly convex quadratic is Gauss–Seidel on the mixed-model equations, which converges because their coefficient matrix is symmetric positive definite.

## Sources

- A. Xavier, D. E. Runcie and D. Habier, *Megavariate methods capture complex genotype-by-environment interactions*, Genetics (2024), <https://doi.org/10.1093/genetics/iyae179>, PMCID PMC12005252 (Efficient solvers, equations (31)–(41)).
