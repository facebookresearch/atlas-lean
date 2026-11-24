# Each EM step for the Gaussian mixture does not decrease the log-likelihood

Let
$x_1, \dots, x_N$ be points of $\mathbb{R}^d$ that are not all equal and let $\theta$ be valid
parameters of a $K$-component isotropic Gaussian mixture. Then $\ell(\theta) \le \ell(\theta^+)$,
where $\ell$ is the log-likelihood of the data under the mixture and $\theta^+$ is the result of
the EM step applied to $\theta$.
