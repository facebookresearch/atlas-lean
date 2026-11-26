# Order conditions for linear multistep methods

Let a [linear multistep method](linear-multistep-method.md) have $\sigma(1) \ne 0$ and [error coefficients](order-of-accuracy-and-error-constants.md) $C_0, C_1, \dots$, and let $p \ge 1$. The method has order of accuracy $p$ if and only if

$$C_0 = C_1 = \cdots = C_p = 0 \quad \text{and} \quad C_{p+1} \ne 0.$$

In that case, for a solution $y$ with $p + 2$ continuous derivatives, the truncation error satisfies

$$T_n = \frac{C_{p+1}}{\sigma(1)}\, h^p\, y^{(p+1)}(x_n) + O(h^{p+1}).$$

For example, the trapezium rule $y_{n+1} - y_n = \tfrac{h}{2}(f_{n+1} + f_n)$ has $C_0 = C_1 = C_2 = 0$ and $C_3 = -\tfrac{1}{12}$, so it has order $2$.

## Depends on

- [Order of accuracy and error constants of a linear multistep method](order-of-accuracy-and-error-constants.md)
- [Linear multistep method](linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.3, expansion (47), Definition 6 and the characterization of the order that follows it. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
- G. Dahlquist, "33 years of numerical instability, Part I", *BIT* 25 (1985), 188–204, Section 3, the definition of the order of consistency, which "leads to $p + 1$ homogeneous linear equations for the $2k + 2$ coefficients of the method", and the expansion (3.4). <https://doi.org/10.1007/BF01934997>
