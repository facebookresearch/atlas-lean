# Effective number of points in an isotropic Gaussian mixture

Given data points
$x_0, \dots, x_{N-1}$ in $\mathbb{R}^d$, valid parameters $\theta$ of a $K$-component isotropic
Gaussian mixture and a component $k$, the effective number of points of $k$ is
$N_k = \sum_n r_{nk}$, where $r_{nk}$ is the responsibility of component $k$ for $x_n$ under
$\theta$, the posterior probability of $k$ given $x_n$.
