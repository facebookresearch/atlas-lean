# No explicit consistent linear multistep method is A-stable

No explicit [consistent](../truncation-error-and-consistency.md) [linear multistep method](../linear-multistep-method.md), that is, none with $\beta_k = 0$, $\rho(1) = 0$ and $\rho'(1) = \sigma(1) \ne 0$, is [A-stable](a-stability.md).

Consistency is needed: $\rho(z) = z - \tfrac12$, $\sigma = 0$ defines an explicit method whose stability polynomial has the root $\tfrac12$ for every $\bar h$.

## Depends on

- [A-stability](a-stability.md)
- [Linear multistep method](../linear-multistep-method.md)
- [Truncation error and consistency of a linear multistep method](../truncation-error-and-consistency.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.1, Theorem 16(i), attributed there to Dahlquist (1963). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
