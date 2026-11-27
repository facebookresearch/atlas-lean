# Quadratic expansion of the log-likelihood ratio

In the setting of [Rao's score test](tendsto-in-distribution-score-statistic.md), with $\ell_n(\theta) = \sum_{i<n} \log p_\theta(X_i)$, let $\delta > 0$ and assume:

- for every $x$ and every $\theta$ with $|\theta - \theta_0| < \delta$, the maps $t \mapsto \log p_t(x)$, $t \mapsto s_t(x)$ and $t \mapsto \partial_t s_t(x)$ are differentiable at $\theta$, and $|\partial_\theta^2 s_\theta(x)| \le M(x)$ for a measurable, $P_{\theta_0}$-integrable $M$;
- $\partial_\theta s_{\theta_0}$ is measurable and integrable with $\mathbb{E}[\partial_\theta s_{\theta_0}(X_0)] = -I(\theta_0)$;
- $\hat\theta_n$ are almost everywhere measurable, $P\big(\sum_{i<n} s_{\hat\theta_n}(X_i) \ne 0\big) \to 0$, $\hat\theta_n \to \theta_0$ in probability, and $\sqrt{n}(\hat\theta_n - \theta_0)$ converges in distribution to some random variable.

Then

$$2\big(\ell_n(\hat\theta_n) - \ell_n(\theta_0)\big) - n(\hat\theta_n - \theta_0)^2 I(\theta_0) \to 0 \quad \text{in probability}.$$

The positivity of $p$ is not used: the expansion holds for any criterion $\log p_\theta(x)$ with these derivatives (with $\log$ of a nonpositive number read as $\log|\cdot|$, and $\log 0 = 0$); the theorems that use it assume $p_\theta(x) > 0$.

## Sources

- S. S. Wilks, *The large-sample distribution of the likelihood ratio for testing composite hypotheses*, Ann. Math. Statist. 9 (1938), 60–62 (second-order expansion).
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Chapter 16.
