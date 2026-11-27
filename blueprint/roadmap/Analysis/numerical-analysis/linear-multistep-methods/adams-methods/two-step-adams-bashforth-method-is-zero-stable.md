# The two-step Adams–Bashforth method is zero-stable

The first characteristic polynomial $\rho(z) = z^2 - z = z(z - 1)$ of the two-step [Adams–Bashforth method](adams-methods.md) has the simple roots $1$ and $0$, so it satisfies the [root condition](../root-condition.md) and the method is [zero-stable](../zero-stability.md). Being also consistent, since $\rho(1) = 0$ and $\rho'(1) = 1 = \sigma(1)$, it is convergent by the [Dahlquist equivalence theorem](../dahlquist-equivalence-theorem.md).

## Depends on

- [Adams methods](adams-methods.md)
- [Zero-stability](../zero-stability.md)
- [Truncation error and consistency of a linear multistep method](../truncation-error-and-consistency.md)
- [Convergence of a linear multistep method](../convergence-of-a-linear-multistep-method.md)
- [Root condition](../root-condition.md)

## Proof depends on

- [Zero-stability and the root condition](../zero-stability-iff-root-condition.md)
- [Dahlquist equivalence theorem](../dahlquist-equivalence-theorem.md)
- [Consistency conditions](../consistency-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.2, Theorem 6 (zero-stability and the root condition), and Section 3.7.2, the two-step Adams–Bashforth row, whose first characteristic polynomial is $z(z - 1)$. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
