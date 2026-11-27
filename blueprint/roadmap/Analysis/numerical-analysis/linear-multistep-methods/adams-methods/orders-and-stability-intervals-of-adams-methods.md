# Orders, error constants and stability intervals of the Adams methods

For $k = 1, 2, 3, 4$ the $k$-step [Adams methods](adams-methods.md) have the following orders $p$, error constants $C_{p+1}$ and intervals of absolute stability $(\alpha, 0)$. The error constants are for the coefficients as written, with $\alpha_k = 1$ and hence $\sigma(1) = 1$; multiplying all coefficients by $s$ multiplies $C_{p+1}$ by $s$.

| $k$ | Adams–Bashforth | $p$ | $C_{p+1}$ | $\alpha$ | Adams–Moulton | $p$ | $C_{p+1}$ | $\alpha$ |
|---|---|---|---|---|---|---|---|---|
| 1 | $y_1 - y_0 = h f_0$ | 1 | $\tfrac12$ | $-2$ | $y_1 - y_0 = \tfrac h2 (f_1 + f_0)$ | 2 | $-\tfrac1{12}$ | $-\infty$ |
| 2 | $y_2 - y_1 = \tfrac h2 (3f_1 - f_0)$ | 2 | $\tfrac5{12}$ | $-1$ | $y_2 - y_1 = \tfrac h{12}(5f_2 + 8f_1 - f_0)$ | 3 | $-\tfrac1{24}$ | $-6$ |
| 3 | $y_3 - y_2 = \tfrac h{12}(23f_2 - 16f_1 + 5f_0)$ | 3 | $\tfrac38$ | $-\tfrac{6}{11}$ | $y_3 - y_2 = \tfrac h{24}(9f_3 + 19f_2 - 5f_1 + f_0)$ | 4 | $-\tfrac{19}{720}$ | $-3$ |
| 4 | $y_4 - y_3 = \tfrac h{24}(55f_3 - 59f_2 + 37f_1 - 9f_0)$ | 4 | $\tfrac{251}{720}$ | $-\tfrac{3}{10}$ | $y_4 - y_3 = \tfrac h{720}(251f_4 + 646f_3 - 264f_2 + 106f_1 - 19f_0)$ | 5 | $-\tfrac{27}{1440}$ | $-\tfrac{90}{49}$ |

For each $k$ the implicit method has the larger interval of absolute stability and the error constant of smaller modulus.

## Depends on

- [Adams methods](adams-methods.md)
- [Order of accuracy and error constants](../order-of-accuracy-and-error-constants.md)
- [Absolute stability of a linear multistep method](../absolute-stability-and-a-stability/absolute-stability.md)

## Proof depends on

- [Order conditions](../order-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.7.2, the lists of $k$-step Adams–Bashforth and Adams–Moulton methods for $k = 1, \dots, 4$ and the remark after them (verification left to the reader there). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
