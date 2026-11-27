# Local power of the likelihood-ratio test

Assume the regularity conditions (R) of [Wald's test](../score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-wald-statistic.md) at $\theta_0$, with $(\theta, x) \mapsto p_\theta(x)$ jointly measurable, all moment and envelope conditions being under the null law $P_{\theta_0} = p_{\theta_0}\nu$, except that the observations now form a triangular array: for each $n$, the row $X_{n,0}, X_{n,1}, \dots$ consists of independent random variables on the probability space $(\Omega, P)$ with law $P_{\theta_n}$, $\theta_n = \theta_0 + h/\sqrt{n}$ for a fixed $h \in \mathbb{R}$. Let $\hat\theta_n$ be almost everywhere measurable, solve the likelihood equation for row $n$ with probability tending to one, $P\big(\sum_{i<n} s_{\hat\theta_n}(X_{n,i}) \ne 0\big) \to 0$, and converge to $\theta_0$ in probability. Then, with $\ell_n(\theta) = \sum_{i<n} \log p_\theta(X_{n,i})$,

$$2\big(\ell_n(\hat\theta_n) - \ell_n(\theta_0)\big) \to \big(Z + h\sqrt{I(\theta_0)}\big)^2 \quad \text{in distribution}, \qquad Z \sim N(0, 1),$$

the noncentral $\chi^2_1$ law with noncentrality $h^2 I(\theta_0)$. For $h = 0$ this is Wilks' theorem for a triangular array.

The row $n = 0$ is irrelevant for the limit; with $h/\sqrt{0}$ read as $0$ its law is $P_{\theta_0}$, which makes $P_{\theta_0}$ a probability measure. No normalisation $\int p_\theta \, d\nu = 1$ is assumed otherwise: the laws $P_{\theta_n}$ are probability measures because they are laws of random variables.

## Sources

- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Chapter 16 (local power), via local asymptotic normality (Chapter 7) and Le Cam's first and third lemmas (Chapter 6).
