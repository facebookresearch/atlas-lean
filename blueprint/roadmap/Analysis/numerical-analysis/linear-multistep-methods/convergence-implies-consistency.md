# Convergence implies consistency

A [convergent](convergence-of-a-linear-multistep-method.md) [linear multistep method](linear-multistep-method.md) is [consistent](truncation-error-and-consistency.md): its characteristic polynomials satisfy $\rho(1) = 0$ and $\rho'(1) = \sigma(1) \ne 0$.

Applying the method to $y' = 0$, $y(0) = 1$ with starting values $y_s = 1$ gives $\rho(1) = \sum_j \alpha_j = 0$. Applying it to $y' = 1$, $y(0) = 0$, whose solution is $y(x) = x$: a convergent method is zero-stable, so $\rho$ has no multiple zero at $1$ and $\rho'(1) \ne 0$, and $y_n = Knh$ with $K = \sigma(1)/\rho'(1)$ is a solution with consistent starting values, whence $K = 1$.

## Depends on

- [Convergence of a linear multistep method](convergence-of-a-linear-multistep-method.md)
- [Truncation error and consistency of a linear multistep method](truncation-error-and-consistency.md)

## Proof depends on

- [Convergence implies zero-stability](convergence-implies-zero-stability.md)
- [Zero-stability is equivalent to the root condition](zero-stability-iff-root-condition.md)
- [Consistency conditions for linear multistep methods](consistency-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.4.1, Theorem 8 and its proof. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
