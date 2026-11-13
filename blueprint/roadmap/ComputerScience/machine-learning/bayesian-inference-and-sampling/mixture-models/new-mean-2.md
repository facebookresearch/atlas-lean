# Mean update of the full-covariance Gaussian mixture

Given data $(x_n)_{n\lt N}$ in
$\mathbb{R}^d$, valid parameters $\theta$ and a component $k$, let $r_{nk}$ be the
responsibility of component $k$ for $x_n$ and let $N_k = \sum_n r_{nk}$. The mean update is the
responsibility-weighted mean

$$\mu_k' = \frac{1}{N_k} \sum_n r_{nk} x_n \in \mathbb{R}^d.$$

When there are no data ($N = 0$), $N_k = 0$ and the convention $N_k^{-1} = 0$ makes
$\mu_k' = 0$.
