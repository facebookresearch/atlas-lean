# Integrated diffusion matrix along a path

For real $\beta$, $\gamma$, a path $x : \mathbb{R} \to \mathbb{R}^2$ and a real $t$, put

$$K(t) = \int_0^t G(x(s))\, ds,$$

with the [infinitesimal covariance](diffusion-matrix.md) $G$, stored as a triple, and the Bochner
integral, which is $0$ when the integrand is not integrable. For the Gaussian martingale $M$ of the
diffusion approximation, $E[(M(s) - M(0))(M(r) - M(0))^{\mathsf T}] = K(\min(s, r))$.
