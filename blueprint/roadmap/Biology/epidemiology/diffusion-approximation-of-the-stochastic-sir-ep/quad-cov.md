# Integrated diffusion matrix along a path

For real $\beta$, $\gamma$, a path $x : \mathbb{R} \to \mathbb{R}^2$ and a real $t$, put

$$K(t) = \int_0^t G(x(s))\, ds,$$

with the [infinitesimal covariance](diffusion-matrix.md) $G$, stored as a triple, and the Bochner
integral, which is $0$ when the integrand is not integrable. If $M$ is a continuous centered
Gaussian martingale with $d\langle M \rangle = G(x(t))\, dt$, then
$E[(M(s) - M(0))(M(r) - M(0))^{\mathsf T}] = K(\min(s, r))$ for $s, r \ge 0$, the matrix compared
entry by entry with the stored triple.
