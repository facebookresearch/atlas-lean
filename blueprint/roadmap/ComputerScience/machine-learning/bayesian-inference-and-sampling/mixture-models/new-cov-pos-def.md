# The covariance update is positive definite

Let $(x_n)_{n\lt N}$ be data in $\mathbb{R}^d$
in general position: $N > 0$, and for every nonzero $v \in \mathbb{R}^d$ the values
$\langle v, x_n \rangle$ are not all equal. Then for all valid parameters $\theta$ of the
$K$-component full-covariance Gaussian mixture and every component $k$, the covariance update
$\Sigma_k'$ (the responsibility-weighted sample covariance of the data about the
responsibility-weighted mean) is positive definite.
