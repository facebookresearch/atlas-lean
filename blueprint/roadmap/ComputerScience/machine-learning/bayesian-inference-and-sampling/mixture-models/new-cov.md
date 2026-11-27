# Covariance update of the full-covariance Gaussian mixture

Given data $(x_n)_{n\lt N}$
in $\mathbb{R}^d$, valid parameters $\theta$ and a component $k$, let $r_{nk}$ be the
responsibility of component $k$ for $x_n$, let $N_k = \sum_n r_{nk}$, and let $\mu_k'$ be the
responsibility-weighted mean $N_k^{-1} \sum_n r_{nk} x_n$. The covariance update is the real
$d \times d$ matrix

$$\Sigma_k' = \frac{1}{N_k} \sum_n r_{nk} (x_n - \mu_k')(x_n - \mu_k')^{\top}.$$

When there are no data ($N = 0$), $N_k = 0$ and the convention $N_k^{-1} = 0$ makes
$\Sigma_k' = 0$.
