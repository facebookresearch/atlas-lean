# Each EM step for the full-covariance Gaussian mixture does not decrease the log-likelihood

**Each EM step for the full-covariance Gaussian mixture does not decrease the
log-likelihood.** Let $x_1, \dots, x_N \in \mathbb{R}^d$ be data in general position (at least
one point, and not all in an affine hyperplane) and let $\theta$ be valid parameters. If
$\theta^{+}$ is the result of one EM step from $\theta$, then $\ell(\theta) \le \ell(\theta^{+})$,
where $\ell$ is the log-likelihood of the data under the mixture.
