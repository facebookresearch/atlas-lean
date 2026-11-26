# Consistency of similarity-based heritability estimating equations

**Setting.** Let $y = X\beta + \epsilon$ with $n$ individuals, a genotype matrix $X \in \mathbb R^{n\times p}$, signal variance $\theta^2 = \operatorname{Var}(X_{i\cdot}^\top\beta)$ and noise variance $\sigma^2_\epsilon$, so that $h^2 = \theta^2/\operatorname{Var}(y_i)$ (taken as $\theta^2$ after scaling $\operatorname{Var}(y_i) = 1$). A **working similarity matrix** is $S = nXWX^\top/\operatorname{Tr}(XWX^\top)$ for a data-dependent weight $W$, so $\operatorname{Tr}(S) = n$. Write $V = \theta^2 S + \sigma^2_\epsilon I$ and the residual $R = yy^\top - V$. The **SMILE estimator** $(\hat\theta^2, \hat\sigma^2_\epsilon)$ solves

$$\operatorname{Tr}(V^{-1}R) = 0, \qquad \operatorname{Tr}(V^{-2}R) = 0.$$

These equations are a linear transform of the Gaussian score equations for $y \mid S \sim N(0, V)$; for $S = XX^\top/p$ they are the [REML equations](../greml-and-haseman-elston-estimation-of-snp-herit/reml-equations-of-is-local-max.md) of the genomic random-effects model. Factor $S = \Phi_S\Phi_S^\top$ with $\Phi_S^\top\Phi_S = \operatorname{Diag}(\lambda_1,\ldots,\lambda_r)$ and write $X\beta = \Phi_S\xi$. Conditions: (C1) $C^{-1} \le r\lambda_i/n \le C$; (C2) eigenvalues and coefficients are asymptotically decoupled, $\sum_{i=1}^r (\xi_i^2/\lVert\xi\rVert^2 - 1/r) f(\lambda_i) \to 0$ for bounded $f$; (C3) $\mathbb E[\xi_i^2 \mid \Lambda] = \tau^2$ with $\operatorname{Cov}(\xi^2 \mid \Lambda)$ well-conditioned. Define the spectral informativeness

$$\Delta_n = \frac1n\sum_{i=1}^r\Big(\frac{r\lambda_i}{n} - 1\Big)^2 + \Big(1 - \frac rn\Big).$$

**Theorem.** Assume the signal and noise have positive variances and finite fourth moments, and $X = Z\Sigma^{1/2}$ with i.i.d. standardized entries of $Z$ having finite eighth moment and $\operatorname{Tr}\Sigma = p$ (Assumption 1).
1. (Theorem 1) Under (C1)–(C2), if $\Delta_n \to \Delta > 0$ in probability, the SMILE estimators are consistent.
2. (Theorem 2) Under (C1) and (C3), $|\hat\theta^2 - \theta^2|$ and $|\hat\sigma^2_\epsilon - \sigma^2_\epsilon|$ are $O_p\big(n^{-1/2} + (n\Delta_n)^{-1/2}\big)$.
3. (Theorem 3 and Corollary 1) For the Gram matrix $S = XX^\top/p$ with $n/p \to c \in (0,1)\cup(1,\infty)$ and well-conditioned non-zero spectrum of $\Sigma$, REML is consistent provided $\beta$ is spectrally isotropic, $\lVert\beta\rVert^{-2}\beta^\top(\Sigma - zI)^{-1}\beta - p^{-1}\operatorname{Tr}(\Sigma - zI)^{-1} \to 0$ for every $z \in \mathbb C^+$; if $\operatorname{rank}\Sigma > n$, the rate is $O_p\big(n^{-1/2} + \sqrt{p^2/(n^2\operatorname{Tr}\Sigma^2)}\big)$.
4. (Corollary 2) For the projection similarity $S = nX(X^\top X)^{-1}X^\top/r_X$ with $r_X/n \to c \in (0,1)$, the SMILE estimators are consistent with $\Delta_n = 1 - r_X/n$, whatever the dependence of $\beta$ on $\Sigma$.

## Depends on

- [GCTA's REML equations at a local maximizer with positive variances](../greml-and-haseman-elston-estimation-of-snp-herit/reml-equations-of-is-local-max.md)

## Expansion

At the true parameters the two estimating equations reduce to spectral averages $\sum_i \lambda_i(\theta^2\lambda_i + \sigma^2_\epsilon)^{-k}(\xi_i^2 - \theta^2)$, $k = 1,2$, so consistency only needs the squared signal coordinates $\xi_i^2$ in the eigenbasis of $S$ to average to $\theta^2$ against any bounded spectral weight, which is condition (C2). The matrix $S = I$ has $\Delta_n = 0$ and cannot separate signal from noise; spread in the spectrum, or a low rank, makes the two equations independent and the rate improves as $\Delta_n$ grows. The classical random-effects (REML or GREML) estimator corresponds to $W = I/p$ and is consistent exactly when the effect vector looks isotropic to the LD spectrum; when effects depend on LD, as under negative selection, a projection-type similarity restores consistency without modelling that dependence.

## Sources

- Jianqiao Wang and Xihong Lin, "Heritability estimation using genetic similarity representation", arXiv:2609.06392 (2026), Section 2 (estimating equations and conditions (C1)–(C3)), Assumption 1, Theorems 1–3, Corollaries 1–2, <https://doi.org/10.48550/arXiv.2609.06392>.
