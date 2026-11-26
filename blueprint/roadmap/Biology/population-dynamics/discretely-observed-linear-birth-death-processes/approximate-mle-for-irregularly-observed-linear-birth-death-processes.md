# Approximate maximum likelihood estimator of the growth rate of an irregularly observed linear birth-death process

Let $X$ be a linear birth-death process with birth rate $\lambda$ and death rate $\mu$, observed at times with gaps $t_1, \dots, t_{n-1} > 0$, giving counts $X_1, \dots, X_n$. Set $\alpha = \lambda - \mu$ and $\sigma^2 = (\lambda + \mu)/(\lambda - \mu)$. Under the Gaussian approximation of the transition law,

$$ X_{i+1} \mid X_i \sim N\!\left( X_i e^{\alpha t_i},\ \sigma^2 X_i e^{\alpha t_i} \bigl(e^{\alpha t_i} - 1\bigr) \right), $$

the score in $\alpha$ of the $i$-th transition splits as $\partial_\alpha l = l_1 + l_2 + l_3$ with

$$ l_1 = \frac{t_i\,[X_{i+1} - X_i e^{\alpha t_i}]}{\sigma^2 (e^{\alpha t_i} - 1)}, \quad l_2 = \frac{t_i\,[X_{i+1} - X_i e^{\alpha t_i}]^2 (2 e^{\alpha t_i} - 1)}{2 X_i \sigma^2 e^{\alpha t_i} (e^{\alpha t_i} - 1)^2}, \quad l_3 = -\frac{t_i}{2} - \frac{t_i e^{\alpha t_i}}{2 (e^{\alpha t_i} - 1)}. $$

**Dominant term (Theorem 1).** As $X_i \to \infty$, $l_2 / l_1 \to 0$ and $l_3 / l_1 \to 0$.

The **approximate MLE** $\hat\alpha$ is the root of the univariate estimating equation

$$ h(\alpha) = \sum_{i=1}^{n-1} \frac{t_i}{e^{\alpha t_i} - 1} \bigl[ X_{i+1} - X_i e^{\alpha t_i} \bigr] = 0, $$

after which $\hat\sigma^2 = \frac{1}{n-1} \sum_{i=1}^{n-1} \frac{X_i e^{\hat\alpha t_i}}{e^{\hat\alpha t_i} - 1} \bigl[ X_{i+1} e^{-\hat\alpha t_i} - X_i \bigr]^2$.

**Properties.** Let $\alpha_0$ be the true growth rate, $T_i = \sum_{j<i} t_j$, and $X_{\min} = \min_i X_i$.

1. (Theorem 2, Corollary 1) As $X_{\min} \to \infty$, the normalized equation $g(\alpha) = h(\alpha) / \bigl(X_1 \sum_i t_i e^{\alpha_0 T_i}\bigr)$ converges to $g^*(\alpha) = \dfrac{\sum_i t_i e^{\alpha_0 T_i} \frac{e^{\alpha_0 t_i} - e^{\alpha t_i}}{e^{\alpha t_i} - 1}}{X_1 \sum_i t_i e^{\alpha_0 T_i}}$, whose root is $\alpha_0$, and $\hat\alpha \to \alpha_0$.
2. (Theorem 3) For $\alpha > 0$, $h$ is asymptotically monotonically decreasing in $\alpha$ as $X_{\min} \to \infty$, so the root is unique in that regime.
3. (Theorem 4) For equidistant gaps $t_i \equiv \tau$, $\hat\alpha$ coincides with the Galton-Watson estimator $\tau^{-1} \log\bigl( \sum_{i \ge 2} X_i / \sum_{i \le n-1} X_i \bigr)$, which is the exact MLE.
4. (Section 4.3, Theorem 5) The same construction extends to time-inhomogeneous linear birth-death processes with conditional mean $X_i \mu_i(\theta)$ and variance $X_i \sigma_i^2(\theta)$, with an analogous limiting estimating function.

Because $h$ is linear in the counts, $\hat\alpha$ is invariant under rescaling all $X_i$ by a common factor, which allows its use on relative quantities such as variant allele frequencies of expanding clones.

## Depends on

- [Transition probabilities of the linear birth-death process and the Galton-Watson estimator](transition-probabilities-of-the-linear-birth-death-process.md)

## Expansion

The mean and variance in the Gaussian approximation are the exact first two moments of the linear birth-death process started from $X_i$ individuals. Since $X_{i+1} - X_i e^{\alpha t_i}$ is of order $\sqrt{X_i}$ under the model, $l_1$ is of order $\sqrt{X_i}$ while $l_2$ and $l_3$ are $O(1)$, giving Theorem 1. Consistency follows because $X_n / (X_1 e^{\alpha_0 T_n}) \to 1$ as $X_1 \to \infty$ (Theorem 6 of the appendix), so each summand of $h$, divided by its deterministic scale, converges, and the limit $g^*$ vanishes exactly at $\alpha = \alpha_0$. For equal gaps the factor $t_i / (e^{\alpha t_i} - 1)$ is common to all summands, so $h(\alpha) = 0$ reduces to $\sum X_{i+1} = e^{\alpha\tau} \sum X_i$.

## Sources

- Xiaochen Long, Marek Kimmel, "An Approximate Maximum Likelihood Estimator for Discretely Observed Linear Birth-and-Death Processes", arXiv (2025). Section 4, Theorems 1-5, Corollary 1, appendix Theorems 6-8. <https://doi.org/10.48550/arXiv.2508.07527>
