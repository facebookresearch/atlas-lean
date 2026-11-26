# Difference isometry for a pre-Brownian integrator

Let $B$ be a pre-Brownian motion (the finite-dimensional laws of Brownian motion) adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $H_1, H_2$ be $F$-progressive with $\mathbb E \int_0^t H_i(u)^2\, du < \infty$. Then
$\int_0^t H_1\, dB - \int_0^t H_2\, dB$ is square integrable and

$$\mathbb E\Bigl[ \Bigl( \int_0^t H_1\, dB - \int_0^t H_2\, dB \Bigr)^2 \Bigr] = \mathbb E \int_0^t \bigl(H_1(u) - H_2(u)\bigr)^2\, du .$$

With linearity, this two-integrand isometry and the formula for elementary integrands determine the
integral on the whole $L^2$ space; path continuity of $B$ is not needed.
