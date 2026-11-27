# Responsibility-weighted scatter in an isotropic Gaussian mixture

Given data points
$x_0, \dots, x_{N-1}$ in $\mathbb{R}^d$, valid parameters $\theta$ of a $K$-component isotropic
Gaussian mixture and a component $k$, the scatter of $k$ is
$S_k = \sum_n r_{nk} \lVert x_n - \mu_k' \rVert^2$, where $r_{nk}$ is the responsibility of
component $k$ for $x_n$ under $\theta$, $N_k = \sum_n r_{nk}$ and
$\mu_k' = N_k^{-1} \sum_n r_{nk} x_n$ is the responsibility-weighted mean.
