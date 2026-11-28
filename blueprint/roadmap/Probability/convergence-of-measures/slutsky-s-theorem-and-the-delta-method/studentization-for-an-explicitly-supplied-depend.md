# Studentization with a consistent covariance estimator

Let $T_L$ be random vectors in $\mathbb R^k$ and $\tau \in \mathbb R^k$ with $\sqrt L(T_L - \tau) \to \mathcal N(0, V)$ in distribution, $V$ positive definite, and let $\hat V_L$
be random symmetric matrices with $\hat V_L \to V$ in probability. Then $\hat V_L$ is positive definite with probability tending to $1$, since the positive definite matrices form an open set,
and, with $\hat V_L^{-1/2}$ defined arbitrarily (for instance as $I_k$) when $\hat V_L$ is not positive definite,

$$\hat V_L^{-1/2} \sqrt L (T_L - \tau) \longrightarrow \mathcal N(0, I_k) \quad \text{in distribution},$$

because $\hat V_L^{-1/2} \to V^{-1/2}$ in probability by [continuous mapping](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/comp-const-of-continuous-at.md) ($A \mapsto A^{-1/2}$ is continuous on
positive definite matrices), and [Slutsky's theorem for a random matrix](slutsky-s-theorem-for-a-random-matrix-times-a-random-vector.md) converging in probability to a constant matrix
multiplying a random vector converging in distribution gives the limit $V^{-1/2} \mathcal N(0, V) = \mathcal N(0, I_k)$; for $k = 1$ this is the
[scalar-multiple form of Slutsky's theorem](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/smul-of-tendsto-in-measure-const.md). The central limit theorem for $T_L$ and the consistency of $\hat V_L$ are hypotheses; for dependent loci they are not
implied by mixing without separate theorems. When $T_L$ is the mean of $B$ independent, identically distributed block means $z_b$ of $m$ loci each ($L = mB$, $B \to \infty$), $V = m \operatorname{Cov}(z_1)$
and $\hat V_L = L\, V_{\mathrm{jack}}$ is consistent for it by the [scaled block-jackknife consistency](../../statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/ae-tendsto-card-smul-jack-cov.md), which gives block-jackknife $Z$-scores.

## Proof depends on

- [Continuous mapping for convergence in probability to a constant](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/comp-const-of-continuous-at.md)
- [Slutsky's theorem for a random matrix times a random vector](slutsky-s-theorem-for-a-random-matrix-times-a-random-vector.md)

## Related topics

- [Slutsky's theorem (scalar-multiple form)](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/smul-of-tendsto-in-measure-const.md)
- [Strong consistency of the scaled block jackknife covariance](../../statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/ae-tendsto-card-smul-jack-cov.md)

## Sources

- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Lemma 2.8 (Slutsky).
