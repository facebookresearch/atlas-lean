# Family mean squared error of an estimator

Let $S$ be a measurable space,
$W : S \to \mathbb{R}$ an estimator, $(P_\theta)_{\theta \in \Theta}$ a family of probability
measures on $S$ and $\tau : \Theta \to \mathbb{R}$ a target function such that
$(W - \tau(\theta))^2$ is integrable for $P_\theta$ for every $\theta \in \Theta$. The family mean
squared error of $W$ is the function on $\Theta$ whose value at $\theta$ is the mean squared error
of $W$ under $P_\theta$ at the target $\tau(\theta)$, that is,
$\int_S (W(x) - \tau(\theta))^2 \, dP_\theta(x)$.

The estimator $W$ is fixed before the family and does not depend on $\theta$.

## Sources

- blueprint `af_fd40353442120bd19166139d`.
