# Common-variance M-step mean

Given weights $w_1, \dots, w_K \in \mathbb{R}$, means
$\mu_1, \dots, \mu_K \in \mathbb{R}^d$, a real $v$ and data $x_1, \dots, x_N \in \mathbb{R}^d$,
the common-variance M-step mean of component $k$ is

$$
\Bigl(\sum_n r_v(x_n, k)\Bigr)^{-1} \sum_n r_v(x_n, k) \, x_n,
$$

where $r_v(x, k)$ is the common-variance responsibility of component $k$ at $x$ for these
weights and means, and $0^{-1} = 0$.
