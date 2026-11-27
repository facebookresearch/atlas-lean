# The log-likelihood is monotone along the ChromHMM iterates

On [rich data](rich.md), for every [valid parameter](valid.md) $\theta_0$, the sequence $k \mapsto \ell(\theta_k)$ is nondecreasing, where $\theta_{k+1}$ is the [ChromHMM step](em-step.md) of $\theta_k$ and $\ell$ the [log-likelihood](log-lik-le-em-step.md).
