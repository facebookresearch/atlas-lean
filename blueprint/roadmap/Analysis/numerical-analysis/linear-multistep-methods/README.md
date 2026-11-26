# Linear multistep methods

A linear $k$-step method $\sum_{j=0}^{k} \alpha_j y_{n+j} = h \sum_{j=0}^{k} \beta_j f(x_{n+j}, y_{n+j})$ uses $k$ previous values to advance the solution of $y' = f(x, y)$. Its first and second characteristic polynomials $\rho$ and $\sigma$ decide its accuracy and stability: consistency is $\rho(1) = 0$, $\rho'(1) = \sigma(1) \ne 0$, zero-stability is the root condition on $\rho$, and Dahlquist's equivalence theorem makes the two together equivalent to convergence. Dahlquist's two barriers bound the order of zero-stable and of A-stable methods.

- [Second-order convergence of the two-step Adams-Bashforth method](second-order-convergence-of-the-two-step-adams-bashforth-method.md)

## Methods, consistency and order

- [Linear multistep method](linear-multistep-method.md)
- [Truncation error and consistency of a linear multistep method](truncation-error-and-consistency.md)
- [Order of accuracy and error constants of a linear multistep method](order-of-accuracy-and-error-constants.md)
- [Order conditions for linear multistep methods](order-conditions.md)
- [Consistency conditions for linear multistep methods](consistency-conditions.md)
- [Order of a linear multistep method from the function ρ(z)/log z − σ(z)](order-via-the-logarithmic-function.md)
- [Maximal order for a given first characteristic polynomial](maximal-order-for-a-given-first-characteristic-polynomial.md)

## Adams methods

- [Adams methods](adams-methods/README.md)

## Zero-stability and convergence

- [Root condition](root-condition.md)
- [Zero-stability](zero-stability.md)
- [Zero-stability is equivalent to the root condition](zero-stability-iff-root-condition.md)
- [Convergence of a linear multistep method](convergence-of-a-linear-multistep-method.md)
- [Convergence implies zero-stability](convergence-implies-zero-stability.md)
- [Convergence implies consistency](convergence-implies-consistency.md)
- [Bounded coefficients of the reciprocal of a root-stable polynomial](bounded-coefficients-of-the-reciprocal-polynomial.md)
- [Error bound for perturbed linear difference equations](error-bound-for-perturbed-linear-difference-equations.md)
- [Consistency and zero-stability imply convergence](consistency-and-zero-stability-imply-convergence.md)
- [Dahlquist equivalence theorem](dahlquist-equivalence-theorem.md)
- [First Dahlquist barrier](first-dahlquist-barrier.md)

## Stability for stiff and nonlinear problems

- [Absolute stability and A-stability](absolute-stability-and-a-stability/README.md)
- [Nonlinear stability of multistep methods](nonlinear-stability/README.md)

## Related topics

- [Runge–Kutta methods](../runge-kutta-methods/README.md): one-step methods, whose stability functions play the part of the stability polynomial.
- [Euler method](../euler-method/README.md): the simplest linear one-step method.
