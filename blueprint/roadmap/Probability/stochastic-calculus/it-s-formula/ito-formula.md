# Itô's formula

Let $B$ be a real Brownian motion under $P$, adapted to a filtration $F$, with increments $B_t - B_s$
($s \le t$) independent of $F_s$, and jointly measurable in $(t, \omega)$. Let $f : \mathbb{R} \to \mathbb{R}$ be of
class $C^2$ with $|f'| \le C$ and $|f''| \le C$. Then for every $t \ge 0$, almost surely,

$$f(B_t) = f(B_0) + \int_0^t f'(B_u)\, dB_u + \frac{1}{2} \int_0^t f''(B_u)\, du,$$

where $\int_0^t f'(B_u)\, dB_u$ is the [$L^2$ Itô integral](../it-integral/ito-integral-2.md) and the last
integral is a pathwise integral, of a continuous function on almost every path.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  Theorem 3.3.3.
