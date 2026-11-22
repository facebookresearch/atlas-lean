# The ChromHMM update maximizes the EM objective

On [rich data](rich.md), for all [valid parameters](valid.md) $\theta, \theta'$,

$$Q(\theta' \mid \theta) \le Q(\hat\theta \mid \theta), \qquad Q(\theta' \mid \theta) = \sum_{n} \sum_{z} p_\theta(z \mid x^{(n)}) \log p_{\theta'}(x^{(n)}, z),$$

where $p$ is the [joint weight](joint.md) and $\hat\theta$ the [ChromHMM step](em-step.md) of $\theta$.
