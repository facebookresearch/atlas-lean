# Non-central chi-square cannot match skewness and kurtosis of a centered Gaussian quadratic form

Let $Q = X^\top A X$ with $X\sim\mathcal{N}(0,\Sigma)$ and $A$ positive semidefinite, and let $\lambda_1,\dots,\lambda_n\ge0$ be the eigenvalues of $\Sigma^{1/2}A\Sigma^{1/2}$, so $Q\overset{d}{=}\sum_i\lambda_iZ_i^2$ with cumulants $c_k = 2^{k-1}(k-1)!\,S_k$, $S_k = \sum_i\lambda_i^k$.

**Littlewood's inequality.** For $\lambda_i\ge0$ and $0<a<b<c$,

$$S_b^{\,c-a} \le S_a^{\,c-b}\,S_c^{\,b-a},$$

with equality if and only if all nonzero $\lambda_i$ are equal.

**Consequence.** The Liu–Tang–Zhang approximation of $Q$ by a shifted and scaled non-central $\chi^2_d(\delta)$ that matches mean, variance, skewness and kurtosis has a solution $(d,\delta)$ if and only if $s_1^2 > s_2$, where, in that method's trace notation, $s_1 = t_3/t_2^{3/2}$ and $s_2 = t_4/t_2^2$ with $t_k = \operatorname{tr}((A\Sigma)^k) + k\,\mu^\top(A\Sigma)^{k-1}A\mu$. For a centered quadratic form $t_k = S_k$, so the condition reads $S_3^2 > S_2S_4$, which Littlewood's inequality with $(a,b,c) = (2,3,4)$ forbids: $S_3^2\le S_2S_4$ always, with equality only when all nonzero weights coincide (the central $\chi^2$ case, e.g. $\Sigma = I$, $A$ a projection). So for any centered Gaussian quadratic form with unequal weights, no non-central chi-square matches skewness and kurtosis simultaneously, and the method silently falls back to skewness-only matching (the Hall–Buckley–Eagleson approximation). This motivates the [moment-ratio gamma approximation](moment-ratio-gamma-approximation-to-gaussian-quadratic-form-tails.md), which keeps information from both moments and always has a solution.

## Depends on

- [Moment-ratio gamma approximation to Gaussian quadratic form tails](moment-ratio-gamma-approximation-to-gaussian-quadratic-form-tails.md)

## Expansion

Write $b = ka + (1-k)c$ with $0<k<1$; then the inequality is $\sum_i\lambda_i^{ka}\lambda_i^{(1-k)c}\le(\sum_i\lambda_i^a)^k(\sum_i\lambda_i^c)^{1-k}$, which is Hölder's inequality with exponents $p = 1/k$, $q = 1/(1-k)$ applied to $x_i = \lambda_i^{ka}$, $y_i = \lambda_i^{(1-k)c}$; equality in Hölder forces $x^p\propto y^q$, i.e. equal $\lambda_i$. Applying this with $(a,b,c) = (2,3,4)$ gives $S_3^2\le S_2S_4$, so the existence condition fails for every centered form with unequal nonzero weights.

## Sources

- H. Zhang, J. Shen, Z. Wu, *An efficient and accurate approximation to the distribution of quadratic forms of Gaussian variables*, arXiv:2005.00905 (2020), Section 2, subsection "Strategies for matching higher moments", Lemma 2.2. <https://doi.org/10.48550/arXiv.2005.00905>
