# Responsibilities with a common variance

Given weights $w_1, \dots, w_K \in \mathbb{R}$,
means $\mu_1, \dots, \mu_K \in \mathbb{R}^d$ and a real $v$, the common-variance responsibility
of component $k$ at a point $x \in \mathbb{R}^d$ is

$$
r_v(x, k) = \frac{w_k \, \mathcal{N}(x \mid \mu_k, vI)}
{\sum_i w_i \, \mathcal{N}(x \mid \mu_i, vI)},
$$

where, for $v > 0$, $\mathcal{N}(x \mid \mu, vI)$ is the isotropic Gaussian density with mean
$\mu$ and covariance $vI$, and for $v \le 0$ it is $1$ if $d = 0$ and $0$ if $d \ge 1$. A quotient
with denominator $0$ is $0$.
