# The natural cubic spline minimizes curvature

Let $f$ have a continuous second derivative on $[a, b]$, let $a = t_0 < t_1 < \cdots < t_n = b$, and let $s$ be the [natural cubic spline](natural-cubic-spline.md) that interpolates $f$ at the knots, $s(t_i) = f(t_i)$. Then

$$\int_a^b \bigl(s''(x)\bigr)^2\, dx \le \int_a^b \bigl(f''(x)\bigr)^2\, dx.$$

So among all twice continuously differentiable interpolants of the data the natural spline has the least integral of the squared second derivative. The proof writes $f = s + g$ with $g(t_i) = 0$ and shows $\int_a^b s'' g'' = 0$ by integrating by parts on each interval, using $s''(a) = s''(b) = 0$ and that the third derivative of $s$ is constant on each interval.

## Depends on

- [Natural cubic spline](natural-cubic-spline.md)
- [Existence and uniqueness of the natural cubic spline](existence-and-uniqueness-of-the-natural-cubic-spline.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.10.2, Theorem 3.22 and its proof. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
