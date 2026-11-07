# M-step of the full-covariance Gaussian mixture

For data
$x_1, \dots, x_N \in \mathbb{R}^d$ and valid parameters $\theta$ with responsibilities $r_{nk}$,
let $N_k = \sum_n r_{nk}$. The M-step parameters have weights $\pi'_k = N_k / N$, means
$\mu'_k = N_k^{-1} \sum_n r_{nk} x_n$ and covariances
$\Sigma'_k = N_k^{-1} \sum_n r_{nk} (x_n - \mu'_k)(x_n - \mu'_k)^{\top}$.
