# Backward differentiation formulas

A *backward differentiation formula* (BDF) is a [linear $k$-step method](../linear-multistep-method.md) whose second characteristic polynomial is $\sigma(z) = \beta_k z^k$:

$$\sum_{j=0}^k \alpha_j y_{n+j} = h \beta_k f_{n+k},$$

with the coefficients chosen to give order $k$. For example, $k = 1$ is the implicit Euler method and $k = 2$ is $y_{n+2} - \tfrac43 y_{n+1} + \tfrac13 y_n = \tfrac23 h f_{n+2}$. The choice is motivated by stiff problems: as $\bar h \to -\infty$ the roots of $\rho - \bar h\sigma$ tend to the roots of $\sigma$, which for a BDF all lie at $0$, so stiff components are strongly damped.

## Depends on

- [Linear multistep method](../linear-multistep-method.md)
- [Order of accuracy and error constants of a linear multistep method](../order-of-accuracy-and-error-constants.md)
- [A(α)-stability](a-alpha-stability.md)
- [Stiff stability](stiff-stability.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.2, the limit argument for the roots of $\pi(\cdot, \bar h)$, the choice $\sigma(z) = \beta_k z^k$, and Table 3. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
