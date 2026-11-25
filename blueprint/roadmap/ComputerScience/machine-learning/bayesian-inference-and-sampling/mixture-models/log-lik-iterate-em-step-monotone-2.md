# The log-likelihood is monotone along the EM iterates of an isotropic Gaussian mixture

Let $x_1, \dots, x_N$ be points of $\mathbb{R}^d$ that are not all equal, let $\theta_0$ be valid
parameters of a $K$-component isotropic Gaussian mixture, and let $\theta_t$ be the result of $t$
EM steps from $\theta_0$. Then $\ell(\theta_t)$ is nondecreasing in $t \in \mathbb{N}$, where
$\ell$ is the log-likelihood of the data under the mixture.
