# Continuous modification of the Itô integral

Let $B$ be a real Brownian motion adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $H$ be $F$-progressive with $\mathbb E \int_0^t H_u^2\, du < \infty$ for every $t \ge 0$. Then there
is a process $J$ with continuous paths (on every sample) such that $J_t = \int_0^t H\, dB$ almost surely for
each $t$. Since the [Itô integral](ito-integral-2.md) is chosen separately at each time, it is only
determined up to a null set that may depend on $t$, so the statement asks for a modification. Any two
continuous modifications are indistinguishable.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 3.2.
