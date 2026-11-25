# The EM theorem for the admixture model

Let $I$ and $J$ be finite, $K$ nonempty, and $g$ a genotype matrix with entries in $\{0, 1, 2\}$ and [allele-copy data](data.md) $x_0, \dots, x_{N-1}$. For [admixture parameters](params.md) $\theta, \theta'$ put

$$\mathcal{Q}(\theta' \mid \theta) = \sum_{n=0}^{N-1} \sum_{k \in K} P_\theta(k \mid x_n) \log p_{\theta'}(x_n, k), \qquad P_\theta(k \mid x) = \frac{p_\theta(x, k)}{\sum_{k'} p_\theta(x, k')},$$

where $p_\theta$ is the [joint weight](joint.md). If $\mathcal{Q}(\theta \mid \theta) \le \mathcal{Q}(\theta' \mid \theta)$, then $\ell_g(\theta) \le \ell_g(\theta')$, where $\ell_g$ is the [admixture log-likelihood](admixture-log-lik.md).
