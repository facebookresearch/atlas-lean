# Wilks' expansion for a triangular array

Let $\mathcal{X}$ be a measurable space, $p : \mathbb{R} \times \mathcal{X} \to \mathbb{R}$ jointly measurable, $s_\theta(x) = \partial_\theta \log p_\theta(x)$ (here and below $\log y = \log|y|$ for $y \ne 0$ and $\log 0 = 0$, as for the [score](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/score.md)), and $\delta > 0$, $I > 0$, $c \in \mathbb{R}$. Suppose that for every $x$ and every $\theta$ with $|\theta - \theta_0| < \delta$ the maps $t \mapsto \log p_t(x)$, $t \mapsto s_t(x)$ and $t \mapsto \partial_t s_t(x)$ are differentiable at $\theta$, and $|\partial_\theta^2 s_\theta(x)| \le M(x)$. Let $(\Omega, P)$ be a probability space, $X_{n,i} : \Omega \to \mathcal{X}$ almost everywhere measurable (row $n$ is the sample of size $n$), and $\hat\theta_n$ almost everywhere measurable estimators that solve the likelihood equation with probability tending to one, $P\big(\sum_{i<n} s_{\hat\theta_n}(X_{n,i}) \ne 0\big) \to 0$, and converge to $\theta_0$ in probability. Assume that

- $-\frac1n \sum_{i<n} \partial_\theta s_{\theta_0}(X_{n,i}) \to I$ and $\frac1n \sum_{i<n} M(X_{n,i}) \to c$ in probability, these averages being almost everywhere measurable;
- the normalised score $n^{-1/2} \sum_{i<n} s_{\theta_0}(X_{n,i})$ converges in distribution to a random variable $Y$.

Then, with $\ell_n(\theta) = \sum_{i<n} \log p_\theta(X_{n,i})$,

$$2\big(\ell_n(\hat\theta_n) - \ell_n(\theta_0)\big) \to \frac{Y^2}{I} \quad \text{in distribution}.$$

No independence or distributional assumption on the rows is made: they enter only through the three limit hypotheses. The positivity of $p$ is not used either: the expansion holds for any criterion $\log p_\theta(x)$ with these derivatives. For i.i.d. rows with law $p_{\theta_0}\nu$ this is Wilks' theorem; under local alternatives it gives the [local power](tendsto-in-distribution-two-mul-log-like-2.md).

## Sources

- S. S. Wilks, *The large-sample distribution of the likelihood ratio for testing composite hypotheses*, Ann. Math. Statist. 9 (1938), 60–62.
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Theorem 5.41 and Chapter 16.
