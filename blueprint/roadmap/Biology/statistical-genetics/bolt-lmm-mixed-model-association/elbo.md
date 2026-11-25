# Mean-field evidence lower bound

Let $X$ be a real $n \times m$ matrix, let $y \in \mathbb{R}^n$, let $\sigma_e^2$ be a real number, let $\pi$ be a measure on $\mathbb{R}$, and let $q_1, \dots, q_m$ be measures on $\mathbb{R}$. The mean-field evidence lower bound is

$$\mathrm{ELBO}(q) = -\frac{n}{2} \log(2\pi\sigma_e^2) - \frac{\mathrm{RSS}(q)}{2\sigma_e^2} - \sum_{j=1}^{m} \mathrm{KL}(q_j \,\|\, \pi),$$

where $\mathrm{RSS}$ is the [expected residual sum of squares](expected-rss.md) and $\mathrm{KL}(q_j \,\|\, \pi) \in [0, \infty]$ is the Kullback–Leibler divergence, counted as $0$ when it is infinite. The conventions $x/0 = 0$ and $\log 0 = 0$, $\log x = \log|x|$ apply when $\sigma_e^2 \le 0$. For [admissible factors](is-admissible.md) all divergences are finite; if moreover $\pi$ is a probability measure and $\sigma_e^2 > 0$, this is the usual evidence lower bound.
