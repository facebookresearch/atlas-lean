# The log-likelihood is monotone along the EM iterates of a full-covariance Gaussian mixture

**The log-likelihood is monotone along the EM iterates of a full-covariance Gaussian
mixture.** Let $x_1, \dots, x_N \in \mathbb{R}^d$ be data in general position: $N > 0$, and for
every nonzero $v \in \mathbb{R}^d$ the values $\langle v, x_n \rangle$ are not all equal. Let
$\theta_0$ be valid parameters of a $K$-component full-covariance Gaussian mixture, and let
$\theta_t$ be the result of $t$ EM steps from $\theta_0$. Then $\ell(\theta_t)$ is nondecreasing
in $t \in \mathbb{N}$, where $\ell$ is the log-likelihood of the data under the mixture's joint
density.
