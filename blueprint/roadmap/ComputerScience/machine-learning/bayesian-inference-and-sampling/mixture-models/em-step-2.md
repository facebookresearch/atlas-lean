# The EM step for isotropic Gaussian mixtures

Let $x_1, \dots, x_N$ be points of
$\mathbb{R}^d$ that are not all equal and let $\theta$ be valid parameters of a $K$-component
isotropic Gaussian mixture. With $r_{nk}$ the responsibility of component $k$ for $x_n$ under
$\theta$ (the E-step), the EM step sends $\theta$ to the valid parameters with weights
$\pi_k' = N_k / N$, means $\mu_k' = N_k^{-1} \sum_n r_{nk} x_n$ and variances
$v_k' = S_k / (d N_k)$, where $N_k = \sum_n r_{nk}$ and $S_k = \sum_n r_{nk} \|x_n - \mu_k'\|^2$
(the M-step).
