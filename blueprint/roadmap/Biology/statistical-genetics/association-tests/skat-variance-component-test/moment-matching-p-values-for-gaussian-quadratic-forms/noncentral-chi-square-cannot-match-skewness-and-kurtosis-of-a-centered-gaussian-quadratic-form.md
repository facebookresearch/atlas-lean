# Non-central chi-square cannot match skewness and kurtosis of a centered Gaussian quadratic form

Let $Q = X^\top A X$ with $X\sim\mathcal{N}(0,\Sigma)$ and $A$ positive semidefinite, and let $\lambda_1,\dots,\lambda_n\ge0$ be the eigenvalues of $\Sigma^{1/2}A\Sigma^{1/2}$, so $Q\overset{d}{=}\sum_i\lambda_iZ_i^2$ with cumulants $c_k = 2^{k-1}(k-1)!\,S_k$, $S_k = \sum_i\lambda_i^k$. Assume $Q$ is non-degenerate, $\Sigma^{1/2}A\Sigma^{1/2} \ne 0$, so that some $\lambda_i > 0$, the variance $c_2$ is positive and the standardized moments are defined (otherwise $Q \equiv 0$).

**Littlewood's inequality.** For $\lambda_i\ge0$ and $0<a<b<c$,

$$S_b^{\,c-a} \le S_a^{\,c-b}\,S_c^{\,b-a},$$

with equality if and only if all nonzero $\lambda_i$ are equal.

**Consequence.** The Liu–Tang–Zhang approximation of $Q$ by a shifted and scaled non-central $\chi^2_d(\delta)$ that matches mean, variance, skewness and kurtosis has a solution $(d,\delta)$ with $\delta > 0$ if and only if $s_1^2 > s_2$, where, in that method's trace notation, $s_1 = t_3/t_2^{3/2}$ and $s_2 = t_4/t_2^2$ with $t_k = \operatorname{tr}((A\Sigma)^k) + k\,\mu^\top(A\Sigma)^{k-1}A\mu$. For a centered quadratic form $t_k = S_k$, so the condition reads $S_3^2 > S_2S_4$, which Littlewood's inequality with $(a,b,c) = (2,3,4)$ forbids: $S_3^2\le S_2S_4$ always, with equality only when all nonzero weights coincide (the central $\chi^2$ case, e.g. $\Sigma = I$, $A$ a projection). So for any non-degenerate centered Gaussian quadratic form with unequal nonzero weights, no non-central chi-square with $\delta > 0$ matches skewness and kurtosis simultaneously, and the method silently falls back to skewness-only matching (the Hall–Buckley–Eagleson approximation). This motivates the [moment-ratio gamma approximation](moment-ratio-gamma-approximation-to-gaussian-quadratic-form-tails.md), which keeps information from both moments and always has a solution.

## Proof depends on

- [Hölder's inequality, geometric-mean form](../../../../../InformationTheory/channel-coding/random-coding-bound-and-gallager-s-exponent/sum-rpow-mul-rpow-le.md)

## Depends on

- [A standard Gaussian quadratic form has a weighted chi-square law](../std-gaussian-map-inner-eq-weighted-chi-s.md)

## Expansion

Write $b = ka + (1-k)c$ with $0<k<1$; then the inequality is $\sum_i\lambda_i^{ka}\lambda_i^{(1-k)c}\le(\sum_i\lambda_i^a)^k(\sum_i\lambda_i^c)^{1-k}$, which is the geometric-mean form of Hölder's inequality applied to $X_i = \lambda_i^a$, $Y_i = \lambda_i^c$ and $\mu = k$, that is Hölder's inequality with exponents $p = 1/k$, $q = 1/(1-k)$ applied to $x_i = \lambda_i^{ka}$, $y_i = \lambda_i^{(1-k)c}$; equality in Hölder forces $x^p\propto y^q$, i.e. equal $\lambda_i$. Applying this with $(a,b,c) = (2,3,4)$ gives $S_3^2\le S_2S_4$, so the existence condition fails for every centered form with unequal nonzero weights.

## Sources

- Hong Zhang, Judong Shen and Zheyang Wu, "A Fast and Accurate Approximation to the Distributions of Quadratic Forms of Gaussian Variables", *Journal of Computational and Graphical Statistics* 31 (2022), 304–311, <https://doi.org/10.1080/10618600.2021.2000423>. Numbering as in the preprint arXiv:2005.00905v2, <https://arxiv.org/abs/2005.00905v2>: Section 2, subsection "Strategies for matching higher moments", Lemma 2.2.
