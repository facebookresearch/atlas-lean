# The pseudo-true value is the Kullback–Leibler projection

Let $X_0, X_1, \dots$ be observations on a probability space with $X_0$ almost everywhere measurable of law $\mu_0$ (a probability measure), $\ell_0$ a $\mu_0$-integrable function, and $Q(\theta) = \mathbb{E}[\ell_\theta(X_0)]$ the expected log-likelihood. Suppose that for every $\theta$ in a set $K$, $\mu_\theta$ a probability measure with $\mu_0 \ll \mu_\theta$, $\ell_\theta$ $\mu_0$-integrable and $\ell_0 - \ell_\theta = \log\frac{d\mu_0}{d\mu_\theta}$ $\mu_0$-almost everywhere. Then $\theta^*$ is the unique maximizer of $Q$ on $K$ if and only if it is the unique minimizer of $\theta \mapsto \mathrm{KL}(\mu_0 \,\|\, \mu_\theta)$ on $K$. The law $\mu_0$ need not belong to the model.

## Sources

- H. White, "Maximum likelihood estimation of misspecified models", *Econometrica* 50 (1982), 1–25.
