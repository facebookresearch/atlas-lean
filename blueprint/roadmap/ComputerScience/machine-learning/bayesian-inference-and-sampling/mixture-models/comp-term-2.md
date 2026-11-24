# Component term of the EM objective for full-covariance Gaussian mixtures

Given points
$x_1, \dots, x_N$ of $\mathbb{R}^d$, valid parameters $\theta$ of a $K$-component
full-covariance Gaussian mixture, a component $k$, a mean $\mu \in \mathbb{R}^d$ and a real
$d \times d$ matrix $S$, the component term is

$$
C_k(\mu, S) = \sum_n r_{nk} \log \mathcal{N}(x_n \mid \mu, S),
$$

where $r_{nk}$ is the responsibility of component $k$ for $x_n$ under $\theta$ and
$\mathcal{N}(\cdot \mid \mu, S)$ is the multivariate Gaussian density with mean $\mu$ and
covariance matrix $S$.

The matrix $S$ is not required to be positive definite; the density is defined for every real
matrix.
