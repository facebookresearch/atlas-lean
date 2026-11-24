# Transmitted photon rate $I_{0,j} e^{-(Ax)_j}$ of a ray

Let the rays be indexed by any set $\iota$ and the attenuation cells by a finite set $\kappa$. For
nonnegative source intensities $I_{0,j}$, a real $\iota \times \kappa$ matrix $A$ and an attenuation
vector $x \in \mathbb{R}^{\kappa}$, the transmitted rate of ray $j$ is the nonnegative real number

$$\lambda_j(x) = I_{0,j}\, e^{-(Ax)_j}, \qquad (Ax)_j = \sum_{k \in \kappa} A_{jk} x_k .$$

The exponential factor is positive, so taking it as a nonnegative real truncates nothing:
[as a real number](transmitted-rate-coe.md) the rate is $I_{0,j} e^{-(Ax)_j}$. The rate is $0$ when
$I_{0,j} = 0$. When there are finitely many rays, it is the rate of the Poisson law of ray $j$ in
the [photon-count law](photon-law.md). In the CT reading, $A_{jk} \ge 0$ is the length of ray $j$ in
cell $k$ and $x_k \ge 0$ the attenuation coefficient of cell $k$, so that
$\lambda_j(x) \le I_{0,j}$; the definition takes any real $A$ and $x$.
