# Bias–variance decomposition of the extended mean squared error

Let $\mu$ be a probability
measure on a measurable space $S$, let $\theta \in \mathbb{R}$, and let $W : S \to \mathbb{R}$ be
square-integrable with respect to $\mu$, that is, $W \in L^2(\mu)$. Then the extended mean squared
error $\int_S (W(x) - \theta)^2 \, d\mu(x)$, computed in $[0, \infty]$, is finite and equals
$\operatorname{Var}_\mu(W) + b^2$, where $b = \int_S W \, d\mu - \theta$ is the bias of $W$ at
$\theta$ under $\mu$.
