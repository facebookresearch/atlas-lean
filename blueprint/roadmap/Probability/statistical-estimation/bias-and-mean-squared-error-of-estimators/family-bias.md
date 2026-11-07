# Family bias of an estimator

Let $S$ be a measurable space, $W : S \to \mathbb{R}$ an
estimator, $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$ such that $W$
is integrable for every $P_\theta$, and $\tau : \Theta \to \mathbb{R}$ a target function. The
family bias of $W$ is the function on $\Theta$ whose value at $\theta$ is the bias of $W$ under
$P_\theta$ at the target $\tau(\theta)$, that is, $\int_S W \, dP_\theta - \tau(\theta)$.

The estimator $W$ is fixed before the family and does not depend on $\theta$.

## Sources

- blueprint `af_723199a7ca6fb3e936a73618`.
