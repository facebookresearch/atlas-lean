# Laplace transforms at the nonnegative integers determine a finite measure on the half-line

Let $\mu$ and $\nu$ be finite Borel measures on $[0, \infty)$ with

$$\int e^{-k x}\, \mu(dx) = \int e^{-k x}\, \nu(dx) \qquad (k = 0, 1, 2, \dots).$$

Then $\mu = \nu$. The images of $\mu$ and $\nu$ under $x \mapsto e^{-x}$ are finite measures on $(0, 1]$ with equal moments of every order, so they are equal
because [compactly supported measures are determined by their moments](../moment-problem-for-compactly-supported-measures/ext-of-forall-integral-pow-eq-of-compl-i.md); since $x \mapsto e^{-x}$ is a measurable bijection of $[0, \infty)$ onto $(0, 1]$ with
measurable inverse, $\mu = \nu$. In particular a finite measure on $[0, \infty)$ is determined by its Laplace transform $s \mapsto \int e^{-s x}\, \mu(dx)$, $s \ge 0$, the measure
analogue of the [one-sided Laplace transform](laplace.md) of a function. This is
uniqueness only: it gives no stability of inversion from approximate values.

## Proof depends on

- [Compactly supported measures are determined by their moments](../moment-problem-for-compactly-supported-measures/ext-of-forall-integral-pow-eq-of-compl-i.md)

## Sources

- W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed., Wiley (1971), Chapter XIII. The reduction to moments is derived above.
