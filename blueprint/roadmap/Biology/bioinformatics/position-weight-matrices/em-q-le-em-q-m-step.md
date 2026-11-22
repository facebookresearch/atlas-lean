# The M-step maximizes the EM objective

Let the alphabet and $Z$ be nonempty, $q(b) > 0$ for every $b$, $\pi(z) > 0$ for every $z$, and let the sequences satisfy the [coverage condition](covers.md). Then for all positive matrices $\theta, \theta'$,

$$Q(\theta' \mid \theta) \le Q(\theta^\ast \mid \theta), \qquad Q(\theta' \mid \theta) = \sum_m \sum_z P(z \mid x^{(m)}, \theta) \log p_{\theta'}(x^{(m)}, z),$$

where $p$ is the [motif model](motif-model.md) and $\theta^\ast$ the [M-step](m-step.md) of $\theta$.
