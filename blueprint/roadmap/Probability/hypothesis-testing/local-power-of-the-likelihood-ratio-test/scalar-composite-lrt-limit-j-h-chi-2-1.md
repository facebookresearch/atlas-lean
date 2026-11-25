# Scalar composite LRT limit (J/H) chi^2_1

Let $Y_1,Y_2,\dots$ be independent with common density $f(\cdot;\theta_0)$, $\theta_0$ an interior point of an open interval $\Theta\subseteq\mathbb R$, and let $c\ell(\theta;y)=\sum_kw_k\log f_k(y;\theta)$ be a composite log-likelihood built from marginal or conditional densities $f_k$, with $c\ell_n(\theta)=\sum_{i=1}^nc\ell(\theta;Y_i)$ and score $u(\theta;y)=\partial_\theta c\ell(\theta;y)$. Let

$$H=\mathbb E_{\theta_0}\bigl[-\partial_\theta u(\theta_0;Y)\bigr]>0,\qquad J=\operatorname{Var}_{\theta_0}\bigl[u(\theta_0;Y)\bigr]>0$$

be the sensitivity and variability. Assume the standard regularity conditions: $c\ell(\cdot;y)$ is twice continuously differentiable near $\theta_0$, $\mathbb E_{\theta_0}u(\theta_0;Y)=0$, $\partial_\theta u$ is dominated near $\theta_0$ by an integrable function, and $\widehat\theta_n$ is a consistent root of $\sum_iu(\theta;Y_i)=0$. Then

$$W_n=2\bigl(c\ell_n(\widehat\theta_n)-c\ell_n(\theta_0)\bigr)\longrightarrow\frac JH\,\chi^2_1\quad\text{in distribution},$$

the law of $(J/H)\,Z^2$ with $Z$ standard normal. Hence, for consistent estimators $\widehat H_n\to H$ and $\widehat J_n\to J$ in probability, the adjusted statistic $(\widehat H_n/\widehat J_n)\,W_n\to\chi^2_1$. When $J=H$ (information unbiasedness, for example a genuine log-likelihood) the limit is $\chi^2_1$, as in [Wilks' theorem](../score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-two-mul-log-like.md). Validity of a block bootstrap for $J$ under linkage is a separate question.

## Depends on

- [The square of a centred Gaussian of variance v has law v χ²₁](../score-wald-and-likelihood-ratio-tests/gaussian-real-map-sq.md)

## Proof depends on

- [Wilks' theorem (simple null)](../score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-two-mul-log-like.md)

## Expansion

A proof page must establish the expansion $W_n=n^{-1}\bigl(\sum_iu(\theta_0;Y_i)\bigr)^2/H+o_P(1)$ from a second-order Taylor expansion around $\widehat\theta_n$, the central limit theorem $n^{-1/2}\sum_iu(\theta_0;Y_i)\to\mathcal N(0,J)$, the identification of the limit of $\bigl(n^{-1/2}\sum_iu\bigr)^2/H$ as $(J/H)\chi^2_1$, Slutsky's lemma for the adjusted statistic, and the case $J=H$.

## Sources

- C. Varin, N. Reid and D. Firth, *An overview of composite likelihood methods*, Statistica Sinica 21 (2011), 5–42, <https://www3.stat.sinica.edu.tw/sstest/oldpdf/A21n11.pdf>, Section 2.3, equation (2.5) and the limit $\sum_j\lambda_jZ_j^2$ with $\lambda_j$ the eigenvalues of $(H^{\psi\psi})^{-1}G_{\psi\psi}$, whose scalar case is $\lambda=J/H$ (statement).
- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, *Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data*, PLoS Genetics 5 (2009), e1000695, <https://journals.plos.org/plosgenetics/article?id=10.1371/journal.pgen.1000695> (bootstrap with linkage; background).
