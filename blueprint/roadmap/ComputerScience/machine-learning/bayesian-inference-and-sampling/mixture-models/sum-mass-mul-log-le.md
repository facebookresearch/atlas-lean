# Isotropic Gaussian mixtures: the weight update maximizes the weights term

Let
$x_1, \dots, x_N$ be $N > 0$ points of $\mathbb{R}^d$, let $\theta$ be valid parameters of a
$K$-component isotropic Gaussian mixture in $d$ dimensions, and let $N_k = \sum_n r_{nk}$ be the
mass of component $k$, where $r_{nk}$ is the responsibility of component $k$ for $x_n$ under
$\theta$. Then for all real $w_1, \dots, w_K > 0$ with $\sum_k w_k = 1$,

$$\sum_k N_k \log w_k \le \sum_k N_k \log \frac{N_k}{N}.$$

That is, the M-step weights $N_k / N$ maximize the weights term (Gibbs' inequality).
