# M-step of the full-covariance Gaussian mixture

For data
$x_1, \dots, x_N \in \mathbb{R}^d$ and valid parameters $\theta$ with responsibilities $r_{nk}$,
let $N_k = \sum_n r_{nk}$. The M-step parameters have weights $\pi'_k = N_k / N$, means
$\mu'_k = N_k^{-1} \sum_n r_{nk} x_n$ and covariances
$\Sigma'_k = N_k^{-1} \sum_n r_{nk} (x_n - \mu'_k)(x_n - \mu'_k)^{\top}$.

Division by zero is read as $0$: for an empty sample ($N = 0$) every weight is $0$, so the
weights do not form a distribution. The result is a tuple of weights, means and covariances; that
it is a valid parameter is a separate statement, under hypotheses on the data.
