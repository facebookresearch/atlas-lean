# Expected log-likelihood of a misspecified model

Let $X_0, X_1, \dots$ be observations on a probability space with $X_0$ almost everywhere measurable of law $\mu_0$ (a probability measure), $\ell_0$ a $\mu_0$-integrable function, and $Q(\theta) = \mathbb{E}[\ell_\theta(X_0)]$ the expected log-likelihood. Let $\mu_\theta$ a probability measure with $\mu_0 \ll \mu_\theta$, $\ell_\theta$ $\mu_0$-integrable and $\ell_0 - \ell_\theta = \log\frac{d\mu_0}{d\mu_\theta}$ $\mu_0$-almost everywhere. Then $Q(\theta) = \int\ell_0\,d\mu_0 - \mathrm{KL}(\mu_0 \,\|\, \mu_\theta)$.
