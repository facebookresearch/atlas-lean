# Occupation of frequency bands

Let $X$ be a regular one-dimensional diffusion on an interval $(a, b)$ with drift $\mu$, infinitesimal variance $\sigma^2$, scale function $S$ and speed density $m = 1/(\sigma^2S')$, started at $p \in (a, b)$ and stopped at its exit time $T^*$ from $(a, b)$. Assume that $S(a)$ and $S(b)$ are finite and that both endpoints are accessible, so that $T^* < \infty$ almost surely. Regularity inside $(a, b)$ does not ensure this: the logistic transform of standard Brownian motion on the real line is regular on $(0, 1)$ with scale function $\log(x/(1 - x))$, never reaches either endpoint, and the kernel below would contain infinite scale values. Under these hypotheses, for continuous $g$ (Karlin and Taylor 1981, Chapter 15)

$$E_p\int_0^{T^*}g(X_s)\,ds = \int_a^bG(p, \xi)\,g(\xi)\,d\xi,$$

with $G(p, \xi) = 2\frac{(S(p) - S(a))(S(b) - S(\xi))}{S(b) - S(a)}m(\xi)$ for $p < \xi < b$ and $G(p, \xi) = 2\frac{(S(b) - S(p))(S(\xi) - S(a))}{S(b) - S(a)}m(\xi)$ for $a < \xi < p$, and, taking $g$ to approximate the indicator of $(x_1, x_2)$, $\int_{x_1}^{x_2}G(p, \xi)\,d\xi$ is the mean time spent in $(x_1, x_2)$ before exit, so that $G$ is the sojourn density (Ewens 2004, Chapter 4). The following consequences are derived from this representation, extended from continuous $g$ to indicators of intervals by monotone approximation.

1. The occupation time $A = \int_0^{T^*}\mathbf 1\{c \le X_s \le d\}\,ds$ of a band $[c, d] \subset (a, b)$ has mean $\int_c^dG(p, \xi)\,d\xi$.
2. Since $G(p, \cdot)$ is continuous on $(a, b)$, $E_p[A]/(d - c) \to G(p, c)$ as $d \downarrow c$.
3. A single interior frequency $y$ has zero expected occupation, $E_p\int_0^{T^*}\mathbf 1\{X_s = y\}\,ds = 0$. A count of generations at one frequency in a population of $M$ gene copies therefore corresponds to the occupation density times the width $1/M$ of a frequency class: in time units of $M$ generations, the expected time spent in a band of width $1/M$ at $y$, divided by $1/M$, tends to $G(p, y)$ as $M \to \infty$ by item 2, which is the sense in which the expected number of generations spent at frequency $i/M = y$ is $G(p, y)$.
4. The moment recursion for additive path functionals with $g = \mathbf 1_{[c,d]}$ and $n = 2$ gives $E_p[A^2] = 2\int_c^dG(p, \xi)\,u(\xi)\,d\xi$ with $u(\xi) = \int_c^dG(\xi, \eta)\,d\eta$, and hence the variance of the band occupation.

## Depends on

- [Dirichlet Green's function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Moment recursion for additive path functionals](../../../Probability/stochastic-calculus/one-dimensional-diffusions/kac-maruyama-kimura-moment-recursion.md)
- [Scale function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/scale-function.md)
- [Speed density of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/speed-density.md)

## Expansion

1. The Green's function $G$ of the diffusion stopped on leaving $(a, b)$, with $S(a)$ and $S(b)$ finite and $a$ and $b$ accessible, as in Karlin and Taylor (1981, Chapter 15); it is obtained from the $[0, 1]$ form by restricting the diffusion to the subinterval (equivalently by an affine change of variable) and is not the $[0, 1]$ formula itself.
2. The band mean from the sojourn-density representation, with the monotone approximation of the indicator by continuous functions.
3. The density limit as the band shrinks, from continuity of $G(p, \cdot)$ away from the diagonal and across it.
4. Zero occupation of single points, and the translation into generations at a frequency class of width $1/M$.
5. The second moment as the case $n = 2$ of the moment recursion, and the variance $E_p[A^2] - E_p[A]^2$.
6. As a separate statement: the limits of the band occupation moments when an endpoint is inaccessible, through interior stopping levels tending to the endpoint.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York, 1981, Chapter 15 (functionals of the diffusion stopped on leaving an interval, and the Green's function in terms of the scale function and speed density).
- W. J. Ewens, *Mathematical Population Genetics I. Theoretical Introduction*, 2nd ed., Springer, New York, 2004, Chapter 4 (sojourn-time densities and mean times spent at a frequency).
