# One-leg twin of a linear multistep method

For the autonomous equation $y' = f(y)$, consider the [linear $k$-step method](../linear-multistep-method.md) $\sum_{j=0}^k \alpha_j y_{n+j} = h \sum_{j=0}^k \beta_j f(y_{n+j})$, written $\rho(E) y_n = h\, \sigma(E) f(y_n)$ with the shift $E y_n = y_{n+1}$, and suppose $s = \sigma(1) \ne 0$. Its *one-leg twin* is defined after normalizing the coefficients so that $\sigma(1) = 1$, that is, after dividing $\rho$ and $\sigma$ by $s$:

$$\rho(E) y_n = h\, s\, f\big(\sigma(E) y_n / s\big), \qquad\text{which for } \sigma(1) = 1 \text{ reads}\qquad \sum_{j=0}^k \alpha_j y_{n+j} = h\, f\Big(\sum_{j=0}^k \beta_j y_{n+j}\Big).$$

Its step equation contains a single evaluation point for $f$, and it does not change when the multistep equation is multiplied by a nonzero constant. For example, the one-leg twin of the trapezium rule is the implicit midpoint rule $y_{n+1} - y_n = h f(\tfrac12(y_{n+1} + y_n))$, also when the trapezium rule is written $2(y_{n+1} - y_n) = h(f(y_n) + f(y_{n+1}))$.

## Depends on

- [Linear multistep method](../linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, the method (95), its one-leg twin (96), the example of the trapezium rule, and the operator form $\rho(E) y_n = h f(\sigma(E) y_n)$. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
- E. Hairer and G. Wanner, *Solving Ordinary Differential Equations II: Stiff and Differential-Algebraic Problems*, 2nd edition, Springer, 1996, Section V.6, (6.5)–(6.6): the normalization $\sigma(1) = 1$ imposed before the one-leg method is associated with a multistep method. <https://doi.org/10.1007/978-3-642-05221-7>
