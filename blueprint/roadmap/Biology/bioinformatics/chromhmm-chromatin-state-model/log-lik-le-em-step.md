# Each ChromHMM step does not decrease the log-likelihood

On [rich data](rich.md), for every [valid parameter](valid.md) $\theta$, $\ell(\theta) \le \ell(\hat\theta)$, where $\hat\theta$ is the [ChromHMM step](em-step.md) and $\ell(\theta) = \sum_n \log \sum_z p_\theta(x^{(n)}, z)$ the log-likelihood of the [joint weight](joint.md).
