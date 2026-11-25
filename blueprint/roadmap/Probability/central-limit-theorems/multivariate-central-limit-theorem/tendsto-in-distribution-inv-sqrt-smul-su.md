# Multivariate central limit theorem

Let $X_0, X_1, \dots$ be independent, identically distributed, square-integrable random vectors in a
finite-dimensional real inner product space $E$, with mean $\mu = \mathbb{E}[X_0]$. If $Y$ is an almost everywhere measurable random vector in $E$ such that, for every $t \in E$, the projection $\langle Y, t \rangle$ is a centered
Gaussian with variance $\operatorname{Var}\langle X_0, t \rangle$, then

$$\frac{1}{\sqrt{n}} \Big( \sum_{k < n} X_k - n\mu \Big) \to Y$$

in distribution. The covariance of $X_0$ may be singular: a projection with variance $0$ has the point
mass at $0$ as its limit.
