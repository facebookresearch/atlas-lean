# The implicit Euler method is A-stable

The implicit Euler method $y_{n+1} = y_n + h f(x_{n+1}, y_{n+1})$, the [linear one-step method](../linear-multistep-method.md) with $\rho(z) = z - 1$ and $\sigma(z) = z$, has stability polynomial $\pi(z; \bar h) = (1 - \bar h) z - 1$. For $\bar h \ne 1$ its only root is $1/(1 - \bar h)$, and $\bar h = 1$ is excluded by the degree condition, so its [region of absolute stability](absolute-stability.md) is exactly $\{\bar h \in \mathbb{C} : |1 - \bar h| > 1\}$, which contains the open left half-plane. Hence the implicit Euler method is [A-stable](a-stability.md).

## Depends on

- [A-stability](a-stability.md)
- [Absolute stability of a linear multistep method](absolute-stability.md)
- [Linear multistep method](../linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.1, the example before Definition 11. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
