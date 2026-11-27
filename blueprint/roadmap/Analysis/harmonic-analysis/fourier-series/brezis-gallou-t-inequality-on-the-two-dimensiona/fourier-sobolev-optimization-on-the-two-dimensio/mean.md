# Mean of a function on the torus

For a continuous function $u : \mathbb{T}^2 \to \mathbb{R}$
on the torus $\mathbb{T}^2 = (\mathbb{R}/2\pi\mathbb{Z})^2$, its mean is
$\int_{(\mathbb{R}/\mathbb{Z})^2} u(2\pi y)\, d\mu(y)$, where $\mu$ is the normalized Haar measure
on the unit torus $(\mathbb{R}/\mathbb{Z})^2$ and $y \mapsto 2\pi y$ is the inverse of the rescaling
to unit period.

Since $\mu$ is a probability measure, this is the average
$(2\pi)^{-2} \int_{[0, 2\pi]^2} u(x)\, dx$; the Lebesgue integral of $u$ over a period cell is
$(2\pi)^2$ times the mean.
