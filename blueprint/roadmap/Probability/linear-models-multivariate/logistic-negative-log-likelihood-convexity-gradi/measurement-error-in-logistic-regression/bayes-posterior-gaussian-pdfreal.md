# The Gaussian Bayes posterior is logistic

Write $\sigma(t) = 1/(1 + e^{-t})$ for the logistic function. For a prior $p \in (0, 1)$ and class-conditional laws $\mathcal N(\mu_0, v)$ and $\mathcal N(\mu_1, v)$ with $v > 0$, the Bayes posterior satisfies, for every $x$,

$$\frac{p\varphi_1(x)}{p\varphi_1(x) + (1 - p)\varphi_0(x)} = \sigma(\alpha + \beta x), \qquad \beta = \frac{\mu_1 - \mu_0}{v},\quad \alpha = \log\frac{p}{1-p} - \beta\,\frac{\mu_0 + \mu_1}{2},$$

where $\varphi_y$ is the density of $\mathcal N(\mu_y, v)$.
