# Closed-form restricted maximum likelihood for latent variance components

**Model.** Expression of $m$ genes in $n$ samples is $Y\in\mathbb{R}^{n\times m}$ with columns $y_i$ (centred). Known confounders form $Z\in\mathbb{R}^{n\times d}$ and $p$ latent variables form $X\in\mathbb{R}^{n\times p}$. For each gene,

$$y_i=Zv_i+Xw_i+\epsilon_i,\qquad \begin{bmatrix}v_i\\w_i\end{bmatrix}\sim\mathcal{N}\Big(0,\begin{bmatrix}B&D\\D^\top&A\end{bmatrix}\Big),\quad \epsilon_i\sim\mathcal{N}(0,\sigma^2I),$$

with $A=\mathrm{diag}(\alpha_1^2,\dots,\alpha_p^2)$, so $y_i\sim\mathcal{N}(0,K)$ with $K=ZBZ^\top+ZDX^\top+XD^\top Z^\top+XAX^\top+\sigma^2I$. With $C=\frac1mYY^\top$ the sample covariance, the negative log-likelihood is (up to constants) $\log\det K+\mathrm{tr}(K^{-1}C)$. Write the SVD $Z=(U_1\ U_2)\binom{\Gamma_1}{0}V^\top$, $C_{11}=U_1^\top CU_1$, $C_{22}=U_2^\top CU_2$ with eigenvalues $\lambda_1\ge\dots\ge\lambda_{n-d}$ and eigenvectors $w_1,\dots,w_{n-d}$, and $W_p=(w_1,\dots,w_p)$.

**Statements.**
1. *(Latent factors only.)* Without known covariates and with $\lambda_p>\lambda_j$ for some $j>p$, the maximum-likelihood solution of $K=XAX^\top+\sigma^2I$ has $\hat x_j=u_j$ (eigenvectors of $C$), $\hat\alpha_j^2=\lambda_j-\hat\sigma^2$ and $\hat\sigma^2=\frac{1}{n-p}\sum_{j>p}\lambda_j$ (probabilistic PCA).
2. *(Known covariates only.)* If $\lambda_{\min}(C_{11})>\mathrm{tr}(C_{22})/(n-d)$, the ML solution of $K=ZBZ^\top+\sigma^2I$ with $B\succeq0$ is $\hat B=V\Gamma_1^{-1}(C_{11}-\hat\sigma^2I)\Gamma_1^{-1}V^\top$, $\hat\sigma^2=\mathrm{tr}(C_{22})/(n-d)$.
3. *(Full model, restricted ML.)* Over latent variables orthogonal to the known ones ($X^\top Z=0$) and diagonal $A\succeq0$, if $\lambda_p>\lambda_j$ for some $j>p$, the restricted ML estimates are

$$\hat X=U_2W_p,\qquad \hat A=\mathrm{diag}(\lambda_1-\hat\sigma^2,\dots,\lambda_p-\hat\sigma^2),\qquad \hat\sigma^2=\frac{1}{n-d-p}\sum_{j=p+1}^{n-d}\lambda_j,$$

and, if $\lambda_{\min}(C_{11})>\hat\sigma^2$, the covariate effects are $\hat B=V\Gamma_1^{-1}(C_{11}-\hat\sigma^2I)\Gamma_1^{-1}V^\top$, $\hat D=V\Gamma_1^{-1}C_{12}W_p$, subject to $B\succeq0$ and $B-DA^{-1}D^\top\succeq0$.
4. *(Characterization.)* $\hat X$ is the set of $p$ orthonormal latent variables orthogonal to $Z$ that minimizes the residual variance $\sigma^2(X)$; equivalently, the latent factors explain the most variance not already explained by the known confounders.

## Depends on

- [Covariance of the mixed-model response](../../quantitative-genetics/linear-mixed-models-and-blup/covariance-mixed-model-response.md)

## Expansion

Rotating samples by $(U_1\ U_2)$ splits the problem into a covariate block and its orthogonal complement. Restricted to the complement (the REML part, free of the fixed covariate directions), the covariance is $U_2^\top XAX^\top U_2+\sigma^2I$, which is the probabilistic PCA problem for $C_{22}$, solved by its top eigenvectors with the noise variance equal to the average discarded eigenvalue. Given the latent variables, the remaining likelihood in $(B,D)$ is maximized by matching the covariate block and the cross block of $C$, subject to positive semidefiniteness, which holds when the covariate-block eigenvalues exceed the noise level. Profiling out all variance parameters for an arbitrary $X$ shows the objective is increasing in $\sigma^2(X)$, giving the minimum-residual-variance characterization.

## Sources

- Muhammad Ammar Malik and Tom Michoel, "Restricted maximum-likelihood method for learning latent variance components in gene expression data with known and unknown confounders", G3 (Bethesda) 12 (2022), jkab410, <https://doi.org/10.1093/g3journal/jkab410>. Numbering follows the arXiv version, arXiv:2005.02921 (2020): model (Methods), Theorems 1–5 and Propositions 1–2, <https://doi.org/10.48550/arXiv.2005.02921>.
