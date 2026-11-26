# Itô isometry, discrete form

Let $B$ be a pre-Brownian motion (the finite-dimensional laws of Brownian motion) adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $H$ be an [elementary integrand](elementary-integrand.md) with times $t_i$ and coefficients
$\xi_i$. Then for every $t \ge 0$,

$$\mathbb E\Bigl[ \Bigl( \int_0^t H\, dB \Bigr)^2 \Bigr] = \sum_i \mathbb E[\xi_i^2] \bigl( \min(t_{i+1}, t) - \min(t_i, t) \bigr) .$$
