# One-leg twin of a linear multistep method

For the autonomous equation $y' = f(y)$, the [linear $k$-step method](../linear-multistep-method.md) $\sum_{j=0}^k \alpha_j y_{n+j} = h \sum_{j=0}^k \beta_j f(y_{n+j})$, written $\rho(E) y_n = h\, \sigma(E) f(y_n)$ with the shift $E y_n = y_{n+1}$, has the *one-leg twin*

$$\sum_{j=0}^k \alpha_j y_{n+j} = h\, f\Big(\sum_{j=0}^k \beta_j y_{n+j}\Big), \qquad\text{that is}\qquad \rho(E) y_n = h\, f(\sigma(E) y_n),$$

which evaluates $f$ once per step. For example, the one-leg twin of the trapezium rule is the implicit midpoint rule $y_{n+1} - y_n = h f(\tfrac12(y_{n+1} + y_n))$.

## Depends on

- [Linear multistep method](../linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, the method (95), its one-leg twin (96), the example of the trapezium rule, and the operator form $\rho(E) y_n = h f(\sigma(E) y_n)$. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
