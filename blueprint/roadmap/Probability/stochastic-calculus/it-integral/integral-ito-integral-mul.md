# Polarized Itô isometry

Let $B$ be a pre-Brownian motion (the finite-dimensional laws of Brownian motion) adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $H$ and $K$ be [elementary integrands](elementary-integrand.md), with possibly different
partitions. Then for every $t \ge 0$,

$$\mathbb E\Bigl[ \Bigl(\int_0^t H\, dB\Bigr) \Bigl(\int_0^t K\, dB\Bigr) \Bigr] = \mathbb E \int_0^t H_u K_u\, du,$$

with the [elementary Itô integrals](ito-integral.md).
