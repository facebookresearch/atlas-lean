# Bias–variance decomposition of the mean squared error

Let $\mu$ be a probability measure
on a measurable space $S$, let $\theta \in \mathbb{R}$, and let $W : S \to \mathbb{R}$ be
square-integrable with respect to $\mu$, that is, $W \in L^2(\mu)$. Then the mean squared error of
$W$ at $\theta$ under $\mu$ equals $\operatorname{Var}_\mu(W) + b^2$, where
$b = \int_S W \, d\mu - \theta$ is the bias of $W$ at $\theta$ under $\mu$.

The integrability that the mean squared error and the bias require follows from $W \in L^2(\mu)$.

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, equation (7.3.1).
