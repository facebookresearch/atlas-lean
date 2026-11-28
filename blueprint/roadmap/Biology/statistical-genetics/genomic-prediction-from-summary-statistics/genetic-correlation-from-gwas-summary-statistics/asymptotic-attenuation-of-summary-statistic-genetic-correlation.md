# Asymptotic attenuation of genetic correlation estimated from GWAS summary statistics

**Model.** Three independent GWAS on $p$ SNPs: discovery GWAS I $(X,y_\alpha)$ of size $n_1$, discovery GWAS II $(Z,y_\beta)$ of size $n_2$, and a target sample $(W,y_\eta)$ of size $n_3$, with additive linear polygenic models

$$y_\alpha=X\alpha+\epsilon_\alpha,\qquad y_\beta=Z\beta+\epsilon_\beta,\qquad y_\eta=W\eta+\epsilon_\eta .$$

The source assumes the following (its Conditions 1 and 2).

- *Genotypes.* The entries of $X$, $Z$, $W$ are independent real random variables with mean $0$, variance $1$ and finite eighth moment (pruned, standardized SNPs).
- *Causal-SNP ratios.* Trait $\alpha$ has $m_\alpha$ causal SNPs, with $m_\alpha/n_1\to\gamma_{\alpha0}\in(0,\infty]$ and $m_\alpha/p\to\omega_{\alpha0}\in[0,1]$, and likewise for $(m_\beta,n_2)$ and $(m_\eta,n_3)$.
- *Overlap.* $m_{\alpha\eta}$ (resp. $m_{\alpha\beta}$) causal SNPs are shared, $\min(m_{\alpha\eta},m_\alpha,m_\eta)\to\infty$ (resp. with $\beta$), and $m_{\alpha\eta}/\sqrt{m_\alpha m_\eta}\to\kappa_{0\alpha\eta}\in(0,1]$, $m_{\alpha\beta}/\sqrt{m_\alpha m_\beta}\to\kappa_{0\alpha\beta}\in(0,1]$.
- *Effects.* The nonzero effects are independent with mean $0$ and finite fourth moments, $\alpha_i$ of variance $\sigma^2_\alpha/p$ (similarly $\sigma^2_\beta/p$, $\sigma^2_\eta/p$, all $\sigma^2>0$); on a shared SNP, $(\alpha_i,\eta_i)$ has mean $0$ and covariance $p^{-1}\begin{pmatrix}\sigma^2_\alpha&\sigma_{\alpha\eta}\\ \sigma_{\alpha\eta}&\sigma^2_\eta\end{pmatrix}$ with $\sigma_{\alpha\eta}=\rho_{\alpha\eta}\sigma_\alpha\sigma_\eta$, and the same for $(\alpha_j,\beta_j)$ with $\rho_{\alpha\beta}$.
- *Errors.* The entries of $\epsilon_\alpha,\epsilon_\beta,\epsilon_\eta$ are independent with mean $0$, positive variances $\sigma^2_{\epsilon_\alpha},\sigma^2_{\epsilon_\beta},\sigma^2_{\epsilon_\eta}$ and finite fourth moments, independent across the three GWAS.

Heritabilities $h^2_\cdot\in(0,1]$ (asymptotically $h^2_\alpha=(m_\alpha/p)\sigma^2_\alpha/\{(m_\alpha/p)\sigma^2_\alpha+\sigma^2_{\epsilon_\alpha}\}$). The *genetic correlation* is the cosine of the effect vectors, $\varphi_{\alpha\eta}=\alpha^\top\eta/(\|\alpha\|\|\eta\|)$ when $\|\alpha\|\|\eta\|>0$ and $0$ otherwise, and $\varphi_{\alpha\eta}=\kappa_{0\alpha\eta}\rho_{\alpha\eta}+o_p(1)$; likewise $\varphi_{\alpha\beta}$.

From the marginal summary statistics $\hat\alpha=n_1^{-1}X^\top y_\alpha$ and $\hat\beta=n_2^{-1}Z^\top y_\beta$, form cross-trait polygenic risk scores on the target, $\hat S_\alpha=W\hat\alpha$ and $\hat S_\beta=W\hat\beta$, and the estimators

$$G_{\alpha\eta}=\frac{y_\eta^\top\hat S_\alpha}{\|y_\eta\|\,\|\hat S_\alpha\|},\qquad G_{\alpha\beta}=\frac{\hat S_\beta^\top\hat S_\alpha}{\|\hat S_\beta\|\,\|\hat S_\alpha\|},\qquad \hat\varphi_{\alpha\beta}=\frac{\hat\alpha^\top\hat\beta}{\|\hat\alpha\|\,\|\hat\beta\|}.$$

**Theorem (all SNPs used).**

1. If $p=c\,(n_1n_3)^a$ with constants $c>0$ and $a\in(0,1)$, then

$$G_{\alpha\eta}=\varphi_{\alpha\eta}+\Big(\sqrt{\frac{n_1}{n_1+p/h^2_\alpha}}\;h_\eta-1\Big)\,\varphi_{\alpha\eta}+o_p(1),$$

while for $a\ge1$, $n_3\,G_{\alpha\eta}=O_p(1)$, so $G_{\alpha\eta}\to0$.

2. If $p^2=c\,(n_1n_2n_3)^a$ with $a\in(0,1)$, then

$$G_{\alpha\beta}=\varphi_{\alpha\beta}+\Big(\sqrt{\frac{n_1}{n_1+p/h^2_\alpha}\cdot\frac{n_2}{n_2+p/h^2_\beta}}-1\Big)\,\varphi_{\alpha\beta}+o_p(1),$$

and for $a\ge1$, $G_{\alpha\beta}\,n_3(n_1+p)(n_2+p)/p^2=O_p(1)$.

3. If $p=c\,(n_1n_2)^a$ with $a\in(0,1)$, the direct summary-statistic estimator $\hat\varphi_{\alpha\beta}$ satisfies the same expansion as $G_{\alpha\beta}$ in item 2; for $a\ge1$, $\hat\varphi_{\alpha\beta}(n_1+p)(n_2+p)/p=O_p(1)$.

The error term is additive: $o_p(1)$ is an absolute error, not a relative factor $\{1+o_p(1)\}$ on the bias (the arXiv v1 version prints the multiplicative form).

Consequently, with $a\in(0,1)$, the bias-corrected estimators

$$G^A_{\alpha\eta}=G_{\alpha\eta}\sqrt{\frac{n_1+p/h^2_\alpha}{n_1h^2_\eta}},\qquad G^A_{\alpha\beta}=G_{\alpha\beta}\sqrt{\frac{(n_1+p/h^2_\alpha)(n_2+p/h^2_\beta)}{n_1n_2}}$$

(and the same factor applied to $\hat\varphi_{\alpha\beta}$) are consistent, $G^A=\varphi+o_p(1)$: for $G^A_{\alpha\eta}$ when $p=c\,n_1^b$ with $b\in(0,1]$, and for $G^A_{\alpha\beta}$ and the corrected $\hat\varphi_{\alpha\beta}$ when $n_1$, $n_2$ and $p$ are proportional. These ratio conditions keep the correction factor bounded, so the additive $o_p(1)$ error stays $o_p(1)$ after rescaling.

## Depends on

## Proof depends on

## Expansion

Under polygenicity each marginal estimate $\hat\alpha_i$ is unbiased but has variance of order $m/n$ rather than $1/n$, because every other causal SNP acts as noise. Summing $p$ such estimates into a score adds $p$ copies of this noise to the score's variance while leaving the covariance with the other trait unchanged, so the cosine is shrunk by $\sqrt{n_1/(n_1+p/h^2_\alpha)}$; the target-side factor $h_\eta$ appears because $y_\eta$ itself contains environmental noise. Remarkably the attenuation does not depend on the unknown numbers of causal SNPs, only on $n_1$, $p$ and the heritabilities, and the target sample size $n_3$ drops out. When $p$ is too large relative to the discovery sample, the noise dominates and the estimator collapses to zero. The proofs use random-matrix limits of quadratic forms in the independent genotype matrices.

## Sources

- B. Zhao, H. Zhu, "On genetic correlation estimation with summary statistics from genome-wide association studies", arXiv:1903.01301 (2019), <https://doi.org/10.48550/arXiv.1903.01301>; published in *Journal of the American Statistical Association* 117(537) (2022) 1–11, Section 2 (Conditions 1 and 2, Definition 1, Theorems 1–3 and the consistent estimators after each), <https://doi.org/10.1080/01621459.2021.1906684> (PMC9232179). The statement follows the published version, whose error terms are additive; the arXiv v1 prints multiplicative ones.
