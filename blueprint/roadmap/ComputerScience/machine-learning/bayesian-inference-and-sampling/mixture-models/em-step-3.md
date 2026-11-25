# EM step for the full-covariance Gaussian mixture

For data
$x_1, \dots, x_N \in \mathbb{R}^d$ in general position (at least one point, and not all in an
affine hyperplane) and valid parameters $\theta$, the EM step returns the M-step parameters of
$\theta$: with responsibilities $r_{nk}$ under $\theta$ and $N_k = \sum_n r_{nk}$, the new
weights are $N_k / N$, the new means are the responsibility-weighted means and the new
covariances are the responsibility-weighted sample covariances. General position makes these
parameters valid.
