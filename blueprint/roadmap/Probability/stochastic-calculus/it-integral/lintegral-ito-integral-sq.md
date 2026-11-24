# Itô isometry

Let $B$ be a pre-Brownian motion (the finite-dimensional laws of Brownian motion) adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $H$ be [Itô-approximable](is-ito-approximable.md) on $[0, t]$. Then, in $[0, \infty]$,
$\mathbb E\bigl[ (\int_0^t H\, dB)^2 \bigr] = \mathbb E \int_0^t H_u^2\, du$, with the [Itô integral](ito-integral-2.md).

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 3.2.
