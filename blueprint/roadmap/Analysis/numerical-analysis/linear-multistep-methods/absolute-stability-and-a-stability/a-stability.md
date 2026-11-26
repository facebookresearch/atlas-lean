# A-stability

A [linear multistep method](../linear-multistep-method.md) is *A-stable* if its [region of absolute stability](absolute-stability.md) $R_A$ contains the whole open left half-plane $\{\bar h \in \mathbb{C} : \operatorname{Re} \bar h < 0\}$.

An A-stable method applied to $y' = \lambda y$ with $\operatorname{Re} \lambda < 0$ produces decaying approximations for every step $h > 0$, so for stiff linear systems its step size is not restricted by stability.

## Depends on

- [Absolute stability of a linear multistep method](absolute-stability.md)
- [Linear multistep method](../linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.1, Definition 11 (due to Dahlquist, 1963). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
