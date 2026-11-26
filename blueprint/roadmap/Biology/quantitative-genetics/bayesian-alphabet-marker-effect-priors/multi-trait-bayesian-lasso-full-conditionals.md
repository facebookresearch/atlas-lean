# Full conditionals of the multiple-trait Bayesian LASSO

Observe $T$ traits on $N$ individuals with model $y_i = \mu + \sum_{j=1}^{p} x_{ij}\beta_j + e_i$, where $\beta_j \in \mathbb{R}^T$ is the effect vector of marker $j$, $x_{ij}$ its genotype code in individual $i$ and $e_i \sim N_T(0, R_0)$ independent. Use the priors $p(\mu, R_0) \propto |R_0|^{-(T+1)/2}$ (flat on $\mu$, Jeffreys on $R_0$), the [multivariate Laplace prior](multivariate-laplace-prior-scale-mixture.md) in its scale-mixture form $\beta_j \mid \Sigma, v_j^2 \sim N_T(0, v_j^2\Sigma)$, $v_j^2 \sim \mathrm{Gamma}(\tfrac{T+1}{2}, \text{rate } \tfrac18)$, and $p(\Sigma) \propto |\Sigma|^{-(T+\nu_\beta+1)/2}\exp\!\big(-\tfrac12\operatorname{tr}(\Sigma^{-1}\Omega_\beta)\big)$.

**Statement.** Writing $S_e = \sum_i (y_i - \mu - \sum_j x_{ij}\beta_j)(y_i - \mu - \sum_j x_{ij}\beta_j)^\top$ and $S_\beta = \sum_{j=1}^p \beta_j\beta_j^\top/v_j^2 + \Omega_\beta$, the full conditional densities are

$$p(R_0 \mid \text{rest}) \propto |R_0|^{-(N+T+1)/2}\exp\!\big(-\tfrac12\operatorname{tr}(R_0^{-1}S_e)\big),$$

$$p(\Sigma \mid \text{rest}) \propto |\Sigma|^{-(p+T+\nu_\beta+1)/2}\exp\!\big(-\tfrac12\operatorname{tr}(\Sigma^{-1}S_\beta)\big),$$

as kernels in $R_0$ and $\Sigma$. In the parametrization with density proportional to $|W|^{-(\nu+T+1)/2}\exp(-\tfrac12\operatorname{tr}(W^{-1}S))$, they have the inverse-Wishart form with $(\nu, S) = (N, S_e)$ and $(p+\nu_\beta, S_\beta)$ (the paper labels them $\mathrm{IW}(N+T, S_e)$ and $\mathrm{IW}(p+T+\nu_\beta, S_\beta)$). Each kernel is a proper inverse-Wishart distribution only when its scale matrix is positive definite and its degrees of freedom satisfy $\nu > T-1$. This can fail for $R_0$: when $N < T$, $S_e$ is a sum of $N$ rank-one matrices in $T$ dimensions and so is singular, and the improper Jeffreys prior does not restore positive definiteness. For $\Sigma$, $S_\beta$ is positive definite whenever $\Omega_\beta$ is. Further,

$$p(v_j^2 \mid \text{rest}) \propto (v_j^2)^{-1/2}\exp\!\left(-\frac{\beta_j^\top\Sigma^{-1}\beta_j}{2v_j^2} - \frac{v_j^2}{8}\right), \qquad j = 1, \dots, p,$$

independently over $j$; this is a generalized inverse Gaussian kernel, which the paper samples by Metropolis–Hastings. Stack by columns, that is observations within each trait: let $Y$ be the $N\times T$ matrix with rows $y_i^\top$, $B$ the $p\times T$ matrix with rows $\beta_j^\top$, $X = (x_{ij})$ the $N\times p$ genotype matrix, $y^* = \operatorname{vec}(Y)$ (the $N$ observations of trait 1, then those of trait 2, and so on) and $\beta^* = \operatorname{vec}(B)$ (the $p$ effects on trait 1, then those on trait 2, and so on). Then $\operatorname{vec}(\text{residuals}) \sim N_{NT}(0, R_0\otimes I_N)$ and $\operatorname{Var}(\beta^*\mid\Sigma, v^2) = \Sigma\otimes D$, and the location parameters $(\mu, \beta^*)$ given the rest are jointly normal with covariance $C^{-1}$ and mean $C^{-1}\big((R_0^{-1}\otimes 1_N^\top)y^*,\ (R_0^{-1}\otimes X^\top)y^*\big)$, where

$$C = \begin{pmatrix} N R_0^{-1} & R_0^{-1}\otimes 1_N^\top X\\ R_0^{-1}\otimes X^\top 1_N & R_0^{-1}\otimes X^\top X + \Sigma^{-1}\otimes D^{-1}\end{pmatrix}, \qquad D = \operatorname{diag}(v_1^2, \dots, v_p^2).$$

## Depends on

- [Multivariate Laplace prior as a normal scale mixture](multivariate-laplace-prior-scale-mixture.md)

## Proof depends on

None beyond reading each kernel off the joint density and Gaussian completion of the square, as the Expansion describes.

## Expansion

Each conditional is read off the joint density $p(y \mid \mu, \beta, R_0)\,p(R_0)\,p(\beta \mid \Sigma, v^2)\,p(v^2)\,p(\Sigma)$. For $\Sigma$, each normal factor contributes $|v_j^2\Sigma|^{-1/2}\exp(-\beta_j^\top\Sigma^{-1}\beta_j/(2v_j^2))$, adding $p/2$ to the exponent of $|\Sigma|^{-1}$ and $\sum_j\beta_j\beta_j^\top/v_j^2$ to the trace term. For $v_j^2$, the normal factor gives $(v_j^2)^{-T/2}$ and the gamma prior $(v_j^2)^{(T+1)/2-1}e^{-v_j^2/8}$, whose product leaves $(v_j^2)^{-1/2}$. With column stacking, $\operatorname{vec}(XB) = (I_T\otimes X)\beta^*$ and $\operatorname{vec}(\mathbf 1_N\mu^\top) = (I_T\otimes\mathbf 1_N)\mu$, so the likelihood precision $R_0^{-1}\otimes I_N$ gives the blocks $(I_T\otimes\mathbf 1_N)^\top(R_0^{-1}\otimes I_N)(I_T\otimes X) = R_0^{-1}\otimes\mathbf 1_N^\top X$ and $R_0^{-1}\otimes X^\top X$ by the mixed-product rule, and $\operatorname{Var}(\beta^* \mid \Sigma, v^2) = \Sigma\otimes D$ produces the block $\Sigma^{-1}\otimes D^{-1}$ in $C$. Stacking traits within individuals instead would require permuting every one of these matrices.

## Sources

- D. Gianola and R. L. Fernando, "A multiple-trait Bayesian Lasso for genome-enabled analysis and prediction of complex traits", Genetics 214 (2020), section "Joint posterior and fully conditional distributions", Equations (17)–(29), <https://doi.org/10.1534/genetics.119.302934> (PMC7017027).
