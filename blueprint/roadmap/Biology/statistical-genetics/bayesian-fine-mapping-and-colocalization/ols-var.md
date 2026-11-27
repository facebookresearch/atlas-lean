# Sampling variance of the least-squares effect estimate

Let $I$ be a finite index set. For a nonnegative real $\sigma^2$ (the residual variance) and a genotype vector $x \in \mathbb{R}^I$, the sampling variance of the [least-squares effect estimate](ols-effect.md) is the nonnegative real

$$s^2(\sigma^2, x) = \frac{\sigma^2}{x^\top x},$$

with the convention that it is $0$ when $x = 0$.
