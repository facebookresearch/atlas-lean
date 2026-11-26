# Consistency conditions for linear multistep methods

A [linear multistep method](linear-multistep-method.md) whose characteristic polynomials satisfy $\sigma(1) \ne 0$ is [consistent](truncation-error-and-consistency.md) if and only if its first two [error coefficients](order-of-accuracy-and-error-constants.md) vanish, $C_0 = C_1 = 0$; equivalently,

$$\rho(1) = 0 \quad \text{and} \quad \rho'(1) = \sigma(1).$$

In particular the first characteristic polynomial of a consistent method has the zero $z = 1$, which is simple because $\rho'(1) = \sigma(1) \ne 0$.

## Depends on

- [Truncation error and consistency of a linear multistep method](truncation-error-and-consistency.md)
- [Order of accuracy and error constants of a linear multistep method](order-of-accuracy-and-error-constants.md)
- [Linear multistep method](linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.3, the paragraph after (47) (necessity of $C_0 = C_1 = 0$), and the proof of Theorem 9, estimate (73) (a method with $C_0 = C_1 = 0$ has $|\sigma(1) T_n| \le K\chi(kh) \to 0$ for continuously differentiable solutions). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
