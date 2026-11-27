# Second Dahlquist barrier

The [order of accuracy](../order-of-accuracy-and-error-constants.md) of an [A-stable](a-stability.md) implicit [linear multistep method](../linear-multistep-method.md) is at most $2$.

Together with the fact that no explicit consistent linear multistep method is A-stable, this limits A-stable linear multistep methods to order $2$; higher-order methods for stiff problems weaken the requirement, as the backward differentiation formulas do.

## Depends on

- [A-stability](a-stability.md)
- [Order of accuracy and error constants of a linear multistep method](../order-of-accuracy-and-error-constants.md)
- [Linear multistep method](../linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.1, Theorem 16(ii), attributed there to Dahlquist (1963). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
