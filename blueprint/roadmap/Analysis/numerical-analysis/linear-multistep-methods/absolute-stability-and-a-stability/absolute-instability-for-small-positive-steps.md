# Consistent zero-stable methods are absolutely unstable for small positive steps

Every [consistent](../truncation-error-and-consistency.md) and [zero-stable](../zero-stability.md) [linear multistep method](../linear-multistep-method.md) is [absolutely unstable](absolute-stability.md) for all sufficiently small positive real $\bar h$: there is $\bar h_0 > 0$ such that for every $0 < \bar h < \bar h_0$ some root of the stability polynomial $\pi(\cdot\,; \bar h) = \rho - \bar h \sigma$ has modulus at least $1$.

This mirrors the exponential growth of the solutions of $y' = \lambda y$ for $\lambda > 0$. If $p \ge 1$ is the order of the method, the order conditions give $\pi(e^{\bar h}; \bar h) = \sum_{q > p} C_q \bar h^q = O(\bar h^{p+1})$, and the root of $\pi(\cdot\,; \bar h)$ that continues the simple zero $1$ of $\rho$ stays within $O(\bar h^{p+1})$ of $e^{\bar h} > 1$.

## Depends on

- [Absolute stability of a linear multistep method](absolute-stability.md)
- [Truncation error and consistency of a linear multistep method](../truncation-error-and-consistency.md)
- [Zero-stability](../zero-stability.md)
- [Linear multistep method](../linear-multistep-method.md)

## Proof depends on

- [Consistency conditions for linear multistep methods](../consistency-conditions.md)
- [Order conditions for linear multistep methods](../order-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.6, Theorem 13 and its proof. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
