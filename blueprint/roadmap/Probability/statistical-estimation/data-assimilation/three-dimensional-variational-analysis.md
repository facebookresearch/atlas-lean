# Three-dimensional variational analysis

Let $B$ and $R$ be symmetric positive definite matrices on finite-dimensional real state and observation spaces, $H$ a real matrix, and
$x_b$, $y$ fixed vectors. The cost $J(x) = \frac12(x - x_b)^{\mathsf T} B^{-1}(x - x_b) + \frac12(Hx - y)^{\mathsf T} R^{-1}(Hx - y)$ has the
unique minimizer

$$x_a = x_b + B H^{\mathsf T}(H B H^{\mathsf T} + R)^{-1}(y - H x_b),$$

from the normal equation $(B^{-1} + H^{\mathsf T} R^{-1} H)(x_a - x_b) = H^{\mathsf T} R^{-1}(y - H x_b)$ and the Woodbury identity. No probability
assumption is used. Identifying $x_a$ with a Gaussian posterior mean needs an independent Gaussian prior and observation-noise model;
nonlinear four-dimensional assimilation and algorithm convergence are outside this result.

## Sources

- F. Bouttier and P. Courtier, *Data assimilation concepts and methods*, ECMWF meteorological training course lecture notes, 1999, the cost function $J(x)$ and the gain $K = BH^{\mathsf T}(HBH^{\mathsf T} + R)^{-1}$, <https://twister.caps.ou.edu/OBAN2019/Assim_concepts.pdf>.
