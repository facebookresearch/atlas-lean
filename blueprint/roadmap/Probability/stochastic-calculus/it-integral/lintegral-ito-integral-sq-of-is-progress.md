# Itô isometry for progressive integrands

Let $B$ be a pre-Brownian motion (the finite-dimensional laws of Brownian motion) adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $H$ be $F$-progressive with $\mathbb E \int_0^t H_u^2\, du < \infty$. Then

$$\mathbb E\Bigl[ \Bigl( \int_0^t H\, dB \Bigr)^2 \Bigr] = \mathbb E \int_0^t H_u^2\, du$$

(an identity in $[0, \infty]$, both sides finite), with the [Itô integral](ito-integral-2.md).

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 3.2.
