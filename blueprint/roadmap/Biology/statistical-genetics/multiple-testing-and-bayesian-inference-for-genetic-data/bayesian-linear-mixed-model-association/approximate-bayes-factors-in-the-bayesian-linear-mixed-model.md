# Approximate Bayes factors in the Bayesian linear mixed model for SNP association

**Model.** For $n$ individuals, a quantitative trait $\mathbf{y}$ follows the linear mixed model

$$
\mathbf{y} = X\mathbf{a} + G\mathbf{b} + \mathbf{u} + \mathbf{e}, \qquad \mathbf{e} \sim \mathrm{N}(\mathbf{0}, \tau^{-1} I), \qquad \mathbf{u} \sim \mathrm{N}(\mathbf{0}, \lambda\tau^{-1} K),
$$

where $X$ holds controlled covariates (intercept, age, sex), $G$ the genotypes of $p$ candidate SNPs with effects $\mathbf{b}$, and $\mathbf{u}$ a random effect with known kinship or population-structure matrix $K$. The Bayesian version (BLMM) puts flat priors on $\mathbf{a}$ (the limit $\Psi^{-1} \to 0$ of $\mathbf{a} \sim \mathrm{N}(\mathbf{0}, \Psi)$), a prior $\mathbf{b} \sim \mathrm{N}(\mathbf{0}, W)$ whose covariance $W$ defines the candidate model, and any proper prior on $(\lambda, \tau)$. The null-based Bayes factor is

$$
\mathrm{BF}(W) = \lim_{\Psi^{-1}\to 0}\frac{P(\mathbf{y}\mid X, G, K, W)}{P(\mathbf{y}\mid X, G, K, W = 0)} .
$$

**Lemma (exact Bayes factor with known variance components).** If $\lambda$ and $\tau$ are known, then with $\hat{\mathbf{b}}$ the generalized least squares estimate of $\mathbf{b}$ and $\hat V = \operatorname{Var}(\hat{\mathbf{b}})$,

$$
\mathrm{BF}(W) = \big|I + \hat V^{-1} W\big|^{-1/2}\exp\Big(\tfrac12\,\hat{\mathbf{b}}^\top \hat V^{-1}\big[W(I + \hat V^{-1}W)^{-1}\big]\hat V^{-1}\hat{\mathbf{b}}\Big).
$$

**Proposition (approximate Bayes factor).** Let $\check\lambda(\kappa)$, $\kappa \in [0,1]$, be a family of estimators of $\lambda$ interpolating between the null-model MLE ($\kappa = 0$) and the full-model MLE ($\kappa = 1$). Let $\check\tau$ be the corresponding estimator of $\tau$, $\check{\mathbf{b}} = \hat{\mathbf{b}}(\check\lambda)$, $\check V = \hat V(\check\lambda, \check\tau)$ and $\check W = W(\check\lambda, \check\tau)$. Then

$$
\mathrm{ABF}(W, \kappa) = \big|I + \check V^{-1}\check W\big|^{-1/2}\exp\Big(\tfrac12\,\check{\mathbf{b}}^\top\check V^{-1}\big[\check W(I + \check V^{-1}\check W)^{-1}\big]\check V^{-1}\check{\mathbf{b}}\Big)
$$

satisfies $\mathrm{BF}(W) = \mathrm{ABF}(W, \kappa)\,(1 + O(1/n))$ for every $\kappa \in [0,1]$. The formula tolerates collinear genotypes and rank-deficient $W$. For a single SNP ($p = 1$), with $\check\omega = \check W$ and $\check v = \check V$, it reduces to Wakefield's approximate Bayes factor

$$
\mathrm{ABF}(\omega, \kappa) = \sqrt{\frac{\check v}{\check v + \check\omega}}\,\exp\Big(\frac12\,\frac{\check\omega}{\check v + \check\omega}\,\frac{\check\beta^2}{\check v}\Big).
$$

## Depends on

- [Wakefield's approximate Bayes factor](../../bayesian-fine-mapping-and-colocalization/wakefield-abf.md)
- [Generalized least-squares matrix](../../../../Probability/linear-models-multivariate/generalized-least-squares/gls-matrix.md)
- [Variance components of the linear mixed model](../../bolt-lmm-mixed-model-association/model.md)

## Expansion

With the variance components fixed, the model is Gaussian and conjugate. Integrating out $\mathbf{u}$ and the flat-prior $\mathbf{a}$ leaves a Gaussian likelihood for $\mathbf{b}$ centred at the GLS estimate $\hat{\mathbf{b}}$ with covariance $\hat V$. Integrating against $\mathrm{N}(\mathbf{0}, W)$ and dividing by the null gives the exact formula. With unknown $(\lambda, \tau)$, a Laplace approximation of the integral over the variance components shows that plugging in any estimator in the family $\check\lambda(\kappa)$ incurs only a relative error $O(1/n)$, because the variance components are estimated at rate $\sqrt n$ and enter the Bayes factor smoothly. As the prior becomes diffuse, $\log\mathrm{ABF}$ is driven by the Wald statistic $\check{\mathbf{b}}^\top\check V^{-1}\check{\mathbf{b}}$, and under small effects it connects to the variance component score statistic used in SNP-set tests, linking Bayesian model comparison to frequentist LMM association tests. Averaging over a grid of $W$ (effect-size scales and burden versus variance-component structures) gives robust SNP-set tests.

## Sources

- Xiaoquan Wen, "Bayesian model comparison in genetic association analysis: linear mixed modeling and SNP set testing", *Biostatistics* 16 (2015), 701–712, <https://doi.org/10.1093/biostatistics/kxv009>; preprint arXiv:1404.7197 (2014), Section 2 (model), Section 3 (Proposition 1 and Remarks 1–2, connection with frequentist test statistics), Appendix A (Lemma 1), <https://doi.org/10.48550/arXiv.1404.7197>.
- J. Wakefield, "Bayes factors for genome-wide association studies: comparison with P-values", Genetic Epidemiology 33 (2009), 79–86, <https://doi.org/10.1002/gepi.20359>.
