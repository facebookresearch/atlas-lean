# The weight update maximizes the weights term of the full-covariance mixture

Let
$(x_n)_{n\lt N}$ be data in $\mathbb{R}^d$ with $N > 0$, let $\theta$ be valid parameters, and let
$N_k = \sum_n r_{nk}$, where $r_{nk}$ is the responsibility of component $k$ for $x_n$. Then for
all real weights $w_k > 0$ with $\sum_k w_k = 1$,

$$\sum_k N_k \log w_k \le \sum_k N_k \log \frac{N_k}{N}.$$

The proof is Gibbs' inequality.
