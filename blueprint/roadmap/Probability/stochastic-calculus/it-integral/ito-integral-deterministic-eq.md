# Wiener's integration by parts

Let $B$ be a real Brownian motion adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $g : \mathbb{R} \to \mathbb{R}$ be of class $C^1$. Then for every $t \ge 0$, almost surely,

$$\int_0^t g(u)\, dB_u = g(t) B_t - g(0) B_0 - \int_0^t g'(u) B_u\, du,$$

the right side being a pathwise integral.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 3.3.
