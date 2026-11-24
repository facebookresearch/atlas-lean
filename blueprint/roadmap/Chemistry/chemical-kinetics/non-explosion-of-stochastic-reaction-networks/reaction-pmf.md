# Law of the next reaction at a state with positive total propensity

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species with
a finite set $\rho$ of reactions, propensities $\lambda_r$ and [total propensity](total-rate.md)
$\lambda$, and let $x \in \mathbb{N}^S$ be a state with $\lambda(x) \ne 0$, that is,
$\lambda(x) > 0$. The law of the reaction that fires at $x$ is the probability distribution on
$\rho$ that gives each reaction $r$ the probability

$$\frac{\lambda_r(x)}{\lambda(x)}.$$

These numbers are nonnegative and sum to $1$. The law is defined only at states with
$\lambda(x) \ne 0$.
