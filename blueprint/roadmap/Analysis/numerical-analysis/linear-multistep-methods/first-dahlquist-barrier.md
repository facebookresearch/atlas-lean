# First Dahlquist barrier

There is no [zero-stable](zero-stability.md) [linear $k$-step method](linear-multistep-method.md) whose [order of accuracy](order-of-accuracy-and-error-constants.md) exceeds $k + 1$ if $k$ is odd, or $k + 2$ if $k$ is even.

Without the stability requirement the $2k + 1$ free coefficients of an implicit $k$-step method allow order $2k$, and the $2k$ of an explicit one allow order $2k - 1$; zero-stability caps the order at about half of that. Simpson's method $y_{n+2} - y_n = \tfrac{h}{3}(f_{n+2} + 4f_{n+1} + f_n)$ is zero-stable of order $4 = k + 2$ with $k = 2$, so the bound is attained.

## Depends on

- [Zero-stability](zero-stability.md)
- [Order of accuracy and error constants of a linear multistep method](order-of-accuracy-and-error-constants.md)
- [Linear multistep method](linear-multistep-method.md)

## Proof depends on

- [Zero-stability is equivalent to the root condition](zero-stability-iff-root-condition.md)
- [Order conditions for linear multistep methods](order-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.5, Theorem 12 and its proof, with the preceding paragraph on the number of free parameters and Example 5. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
