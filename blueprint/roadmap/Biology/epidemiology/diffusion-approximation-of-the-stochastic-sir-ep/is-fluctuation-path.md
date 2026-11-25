# Solution of the linear fluctuation equation

For real $\beta$, $\gamma$ and $T$, a path $x : \mathbb{R} \to \mathbb{R}^2$, an initial value
$u_0 \in \mathbb{R}^2$ and a driving path $m : \mathbb{R} \to \mathbb{R}^2$, a path $U$ solves the
linear fluctuation equation on $[0, T]$ if $U$ is continuous on $[0, T]$ and

$$
U(t) = u_0 + \bigl(m(t) - m(0)\bigr) + \int_0^t DF(x(s))\, U(s)\, ds
\quad \text{for } t \in [0, T],
$$

with the [Jacobian](jacobian.md) $DF$ and the Bochner integral, which is $0$ when the integrand is
not integrable; when $x$ is continuous on $[0, T]$ the integrand is continuous there. The driving
path enters only through its increments, so $U(0) = u_0$ [for every](initial.md) $m$ when
$T \ge 0$. Driven by a Gaussian martingale
starting at $0$, this is the stochastic equation $dU = DF(x(t))\, U\, dt + dM(t)$ of the diffusion
approximation, solved path by path.
