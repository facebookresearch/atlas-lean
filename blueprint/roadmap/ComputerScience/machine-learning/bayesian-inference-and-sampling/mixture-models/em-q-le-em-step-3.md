# The M-step of the full-covariance Gaussian mixture maximizes the EM objective

Let
$x_1, \dots, x_N \in \mathbb{R}^d$ be data in general position: $N > 0$, and for every nonzero
$v \in \mathbb{R}^d$ the values $\langle v, x_n \rangle$ are not all equal. Let $\theta$ be valid
parameters of a $K$-component full-covariance Gaussian mixture, and let $\theta^+$ be the result
of the EM step applied to $\theta$. Then every valid parameter $\theta'$ satisfies
$Q(\theta' \mid \theta) \le Q(\theta^+ \mid \theta)$, where $Q$ is the EM objective of the
mixture's joint density.
