# The trapezium rule is the most accurate second-order A-stable method

Among the [A-stable](a-stability.md) [linear multistep methods](../linear-multistep-method.md) of [order](../order-of-accuracy-and-error-constants.md) $2$, the trapezium rule

$$y_{n+1} - y_n = \tfrac{h}{2}\bigl(f(x_{n+1}, y_{n+1}) + f(x_n, y_n)\bigr)$$

has the smallest error constant in absolute value. The error constant $C_3$ is compared for methods normalized so that $\sigma(1) = 1$, as the trapezium rule is; multiplying all coefficients by a nonzero constant does not change a method, but scales $C_3$. For the trapezium rule $C_3 = -\tfrac{1}{12}$.

## Depends on

- [A-stability](a-stability.md)
- [Order of accuracy and error constants of a linear multistep method](../order-of-accuracy-and-error-constants.md)
- [Linear multistep method](../linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.1, Theorem 16(iii), attributed there to Dahlquist (1963); the normalization $\sigma(1) = 1$ makes the comparison of error constants meaningful and matches the truncation error $T_n = (C_3/\sigma(1)) h^2 y'''(x_n) + O(h^3)$ of Section 3.3. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
