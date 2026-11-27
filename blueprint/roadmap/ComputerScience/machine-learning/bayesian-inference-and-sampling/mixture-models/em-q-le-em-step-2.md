# The M-step for isotropic Gaussian mixtures maximizes the EM objective

Let
$x_1, \dots, x_N$ be points of $\mathbb{R}^d$ that are not all equal, let $\theta$ be valid
parameters of a $K$-component isotropic Gaussian mixture, and let $\theta^+$ be the result of
the EM step applied to $\theta$. Then every valid parameter $\theta'$ satisfies
$Q(\theta' \mid \theta) \le Q(\theta^+ \mid \theta)$, where $Q$ is the EM objective of the
mixture's joint density.
