# Additivity of the Itô integral

Let $B$ be a real Brownian motion adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $H_1, H_2$ be $F$-progressive with $\mathbb E \int_0^t H_i(u)^2\, du < \infty$. Then almost surely
$\int_0^t (H_1 + H_2)\, dB = \int_0^t H_1\, dB + \int_0^t H_2\, dB$, with the [Itô integral](ito-integral-2.md).
Together with homogeneity and the difference isometry this determines the integral on the whole $L^2$
space of progressive integrands.
