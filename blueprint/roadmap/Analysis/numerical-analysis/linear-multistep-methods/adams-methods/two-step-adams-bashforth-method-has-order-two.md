# The two-step Adams–Bashforth method has order two

The two-step [Adams–Bashforth method](adams-methods.md)

$$y_{n+2} - y_{n+1} = \frac{h}{2}\,(3 f_{n+1} - f_n),$$

with $\rho(z) = z^2 - z$ and $\sigma(z) = (3z - 1)/2$, has [order of accuracy](../order-of-accuracy-and-error-constants.md) exactly $2$, with error constant

$$C_3 = \sum_{j} \frac{j^3 \alpha_j}{3!} - \sum_j \frac{j^2 \beta_j}{2!} = \frac{8 - 1}{6} - \frac{3}{4} = \frac{5}{12},$$

and its interval of absolute stability is $(-1, 0)$.

## Depends on

- [Adams methods](adams-methods.md)
- [Order of accuracy and error constants](../order-of-accuracy-and-error-constants.md)

## Proof depends on

- [Order conditions](../order-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.7.2, the list of $k$-step Adams–Bashforth methods, item (2): $k = 2$, $p^* = 2$, $C_{p^*+1} = 5/12$, $\alpha = -1$ (the verification is left to the reader there). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
