# The Itô integral is well defined

Let $B$ be a pre-Brownian motion (the finite-dimensional laws of Brownian motion) adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $H$ have a jointly measurable [restriction to $(0, t]$](restrict-ioc.md), and let $K^{(n)}$ be any
sequence of [elementary integrands](elementary-integrand.md) with $d_t(K^{(n)}, H) \to 0$ ([integrand
distance](integrand-dist.md)). Then the [elementary Itô integrals](ito-integral.md) $\int_0^t K^{(n)}\, dB$
converge in $L^2(P)$ to the [$L^2$ Itô integral](ito-integral-l2.md) $\int_0^t H\, dB$.
