# Debiased ridge MVMR estimator under many weak instruments

**Data model.** For SNPs $j = 1,\dots,p$, two-sample GWAS summary statistics give SNP–exposure associations $\hat{\boldsymbol\gamma}_j \sim N(\boldsymbol\gamma_j, \Sigma_{Xj})$ for $K$ exposures and SNP–outcome associations $\hat\Gamma_j \sim N(\Gamma_j, \sigma_{Yj}^2)$, all $2p$ statistics mutually independent, with the MVMR model

$$\Gamma_j = \boldsymbol\gamma_j^\top \boldsymbol\beta_0,$$

where $\boldsymbol\beta_0 \in \mathbb R^K$ are the direct causal effects. The variances are known, $\Sigma_{Xj} = \operatorname{diag}(\sigma_{Xjk})\,\Sigma\,\operatorname{diag}(\sigma_{Xjk})$ with a shared correlation matrix $\Sigma$ allowing sample overlap among exposure GWASs, and $n, p, K$ grow. Let $\hat\Pi$ be the $p\times K$ matrix with rows $\hat{\boldsymbol\gamma}_j^\top$, $W = \operatorname{diag}(\sigma_{Yj}^{-2})$, $V = \sum_j \Sigma_{Xj}\sigma_{Yj}^{-2}$, $M_j = \boldsymbol\gamma_j\boldsymbol\gamma_j^\top\sigma_{Yj}^{-2}$, $V_j = \Sigma_{Xj}\sigma_{Yj}^{-2}$, and let $\mu_{n,\min}$ be the instrument strength along the weakest direction (the smallest of the rates $\mu_{nk}$ that normalize $\sum_j M_j$).

**Estimator.** With $(\cdot)_+$ the projection onto positive semidefinite matrices and a ridge parameter $\phi \ge 0$,

$$\hat{\boldsymbol\beta}_{\rm dRidge} = \arg\min_{\boldsymbol\beta}\ \tfrac12 \boldsymbol\beta^\top(\hat\Pi^\top W\hat\Pi - V)_+\boldsymbol\beta - \hat{\boldsymbol\Gamma}^\top W\hat\Pi\boldsymbol\beta + \phi\|\boldsymbol\beta\|_2^2 = \big((\hat\Pi^\top W\hat\Pi - V)_+ + \phi I_K\big)^{-1}\hat\Pi^\top W\hat{\boldsymbol\Gamma}.$$

The term $-V$ removes the bias $\mathbb E[\hat\Pi^\top W\hat\Pi] - \Pi^\top W \Pi = V$ caused by noise in $\hat{\boldsymbol\gamma}_j$.

**Theorem.** Assume $\mu_{n,\min}/\sqrt p \to \infty$ and $\max_j \gamma_{jk}^2\sigma_{Xjk}^{-2}/(\mu_{n,\min} + p) \to 0$ for every $k$ (no single SNP dominates). If $\phi = o_P(\sqrt{\mu_{n,\min} + p})$, then $\hat{\boldsymbol\beta}_{\rm dRidge}$ is consistent and

$$\mathbb V^{-1/2}\Big(\sum_{j=1}^p M_j\Big)\big(\hat{\boldsymbol\beta}_{\rm dRidge} - \boldsymbol\beta_0\big) \xrightarrow{d} N(\mathbf 0, I_K), \qquad \mathbb V = \sum_{j=1}^p\Big\{(1 + \boldsymbol\beta_0^\top V_j\boldsymbol\beta_0)(M_j + V_j) + V_j\boldsymbol\beta_0\boldsymbol\beta_0^\top V_j\Big\}.$$

The rate condition allows instruments that are individually weak: in the typical regime $\mu_{n,\min} = \Theta(p)$ it holds automatically.

## Depends on

- [Inverse-variance weighted estimator](../mendelian-randomization/ivw.md)

## Expansion

Write $\hat{\boldsymbol\beta} - \boldsymbol\beta_0 = A^{-1}\big(\hat\Pi^\top W(\hat{\boldsymbol\Gamma} - \hat\Pi\boldsymbol\beta_0) + V\boldsymbol\beta_0 - \phi\boldsymbol\beta_0\big)$ with $A$ the regularized debiased Gram matrix. The score $\sum_j \sigma_{Yj}^{-2}\hat{\boldsymbol\gamma}_j(\hat\Gamma_j - \hat{\boldsymbol\gamma}_j^\top\boldsymbol\beta_0) + V\boldsymbol\beta_0$ has mean zero and is a sum of independent terms whose covariance is $\mathbb V$; the Lindeberg condition is the no-dominant-SNP assumption, while $\mu_{n,\min}/\sqrt p \to \infty$ makes the noise in $A$ negligible relative to $\sum_j M_j$. The ridge term contributes $\phi\,\mathbb V^{-1/2}\boldsymbol\beta_0$, which vanishes under the stated rate on $\phi$.

## Sources

- Yinxiang Wu, Neil M. Davies, Ting Ye, "Group Identification and Variable Selection in Multivariable Mendelian Randomization with Highly Correlated Exposures", arXiv (2025). Supplementary Assumptions 1–2, MVMR-dRidge definition, Theorem 2. <https://doi.org/10.48550/arXiv.2511.12375>
