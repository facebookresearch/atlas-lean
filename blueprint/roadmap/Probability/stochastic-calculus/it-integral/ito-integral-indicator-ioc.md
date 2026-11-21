# Itô integral of a single-step integrand

Let $B$ be a pre-Brownian motion (the finite-dimensional laws of Brownian motion) adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $a \le b$ and $\xi$ be $F_a$-measurable with $|\xi| \le C$. Then for every $t \ge 0$, almost surely,

$$\int_0^t \xi\, \mathbf 1_{(a, b]}(u)\, dB_u = \xi \bigl( B_{\min(b, t)} - B_{\min(a, t)} \bigr) .$$

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 3.2.A.
