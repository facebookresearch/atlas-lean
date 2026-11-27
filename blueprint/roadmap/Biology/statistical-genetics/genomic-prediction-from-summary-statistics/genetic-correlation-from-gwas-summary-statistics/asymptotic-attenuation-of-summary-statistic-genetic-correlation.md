# Asymptotic attenuation of genetic correlation estimated from GWAS summary statistics

**Model.** Three independent GWAS on $p$ SNPs (pruned to be independent and standardized; entries independent with mean $0$, variance $1$ and finite eighth moment): discovery GWAS I $(X,y_\alpha)$ of size $n_1$, discovery GWAS II $(Z,y_\beta)$ of size $n_2$, and a target sample $(W,y_\eta)$ of size $n_3$, with additive linear polygenic models

$$y_\alpha=X\alpha+\epsilon_\alpha,\qquad y_\beta=Z\beta+\epsilon_\beta,\qquad y_\eta=W\eta+\epsilon_\eta .$$

Each trait has $m_\cdot\to\infty$ causal SNPs with independent effects of variance $\sigma^2_\cdot$ and finite fourth moments; shared causal SNPs have effect correlation $\rho$, and the overlap fractions $m_{\alpha\eta}/\sqrt{m_\alpha m_\eta}$ converge. Heritabilities $h^2_\cdot\in(0,1]$. The *genetic correlation* is the cosine of the effect vectors, $\varphi_{\alpha\eta}=\alpha^\top\eta/(\|\alpha\|\|\eta\|)$, asymptotically $\kappa_{0\alpha\eta}\rho_{\alpha\eta}$.

From the marginal summary statistics $\hat\alpha=n_1^{-1}X^\top y_\alpha$ and $\hat\beta=n_2^{-1}Z^\top y_\beta$, form cross-trait polygenic risk scores on the target, $\hat S_\alpha=W\hat\alpha$ and $\hat S_\beta=W\hat\beta$, and the estimators

$$G_{\alpha\eta}=\frac{y_\eta^\top\hat S_\alpha}{\|y_\eta\|\,\|\hat S_\alpha\|},\qquad G_{\alpha\beta}=\frac{\hat S_\beta^\top\hat S_\alpha}{\|\hat S_\beta\|\,\|\hat S_\alpha\|},\qquad \hat\varphi_{\alpha\beta}=\frac{\hat\alpha^\top\hat\beta}{\|\hat\alpha\|\,\|\hat\beta\|}.$$

**Theorem (all SNPs used).**

1. If $p=c\,(n_1n_3)^a$ with $a\in(0,1)$, then

$$G_{\alpha\eta}=\varphi_{\alpha\eta}+\Big(\sqrt{\frac{n_1}{n_1+p/h^2_\alpha}}\;h_\eta-1\Big)\,\varphi_{\alpha\eta}\,\{1+o_p(1)\},$$

while for $a\ge1$, $n_3\,G_{\alpha\eta}=O_p(1)$, so $G_{\alpha\eta}\to0$.

2. If $p^2=c\,(n_1n_2n_3)^a$ with $a\in(0,1)$, then

$$G_{\alpha\beta}=\varphi_{\alpha\beta}+\Big(\sqrt{\frac{n_1}{n_1+p/h^2_\alpha}\cdot\frac{n_2}{n_2+p/h^2_\beta}}-1\Big)\,\varphi_{\alpha\beta}\,\{1+o_p(1)\},$$

and for $a\ge1$, $G_{\alpha\beta}\,n_3(n_1+p)(n_2+p)/p^2=O_p(1)$.

3. If $p=c\,(n_1n_2)^a$ with $a\in(0,1)$, the direct summary-statistic estimator $\hat\varphi_{\alpha\beta}$ satisfies the same expansion as $G_{\alpha\beta}$ in item 2; for $a\ge1$, $\hat\varphi_{\alpha\beta}(n_1+p)(n_2+p)/p=O_p(1)$.

Consequently the bias-corrected estimators

$$G^A_{\alpha\eta}=G_{\alpha\eta}\sqrt{\frac{n_1+p/h^2_\alpha}{n_1h^2_\eta}},\qquad G^A_{\alpha\beta}=G_{\alpha\beta}\sqrt{\frac{(n_1+p/h^2_\alpha)(n_2+p/h^2_\beta)}{n_1n_2}}$$

(and the same factor applied to $\hat\varphi_{\alpha\beta}$) are consistent for $\varphi$, i.e. equal $\varphi\{1+o_p(1)\}$, when $n_1,n_2,p$ are comparable.

In each item the error term multiplies only the bias $(\cdot-1)\varphi$, not the whole leading term.

## Depends on

## Proof depends on

## Expansion

Under polygenicity each marginal estimate $\hat\alpha_i$ is unbiased but has variance of order $m/n$ rather than $1/n$, because every other causal SNP acts as noise. Summing $p$ such estimates into a score adds $p$ copies of this noise to the score's variance while leaving the covariance with the other trait unchanged, so the cosine is shrunk by $\sqrt{n_1/(n_1+p/h^2_\alpha)}$; the target-side factor $h_\eta$ appears because $y_\eta$ itself contains environmental noise. Remarkably the attenuation does not depend on the unknown numbers of causal SNPs, only on $n_1$, $p$ and the heritabilities, and the target sample size $n_3$ drops out. When $p$ is too large relative to the discovery sample, the noise dominates and the estimator collapses to zero. The proofs use random-matrix limits of quadratic forms in the independent genotype matrices.

## Sources

- B. Zhao, H. Zhu, "On genetic correlation estimation with summary statistics from genome-wide association studies", arXiv:1903.01301 (2019), Section "Cross-trait PRS with all SNPs": Condition 1, Condition 2, Definition 1, Theorems 1, 2 and 3 and Remarks 2–3, <https://doi.org/10.48550/arXiv.1903.01301>; published in *Journal of the American Statistical Association* 117(537) (2022) 1–11, <https://doi.org/10.1080/01621459.2021.1906684>. Locators follow arXiv v1.
