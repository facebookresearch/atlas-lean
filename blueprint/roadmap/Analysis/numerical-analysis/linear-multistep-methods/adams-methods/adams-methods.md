# Adams methods

A [linear $k$-step method](../linear-multistep-method.md) whose first characteristic polynomial is

$$\rho(z) = z^k - z^{k-1}$$

is called an *Adams method*; it advances $y_{n+k} = y_{n+k-1} + h \sum_{j=0}^{k} \beta_j f_{n+j}$. Since the roots of $\rho$ are $1$ and, for $k \ge 2$, $0$, every Adams method is [zero-stable](../zero-stability.md). The particular *Adams–Bashforth* and *Adams–Moulton* methods choose the $\beta_j$ by replacing $f(x, y(x))$ in $y(x_{n+k}) - y(x_{n+k-1}) = \int_{x_{n+k-1}}^{x_{n+k}} f(x, y(x))\,dx$ by its polynomial interpolant:

- the $k$-step Adams–Bashforth method interpolates at the $k$ nodes $x_n, \dots, x_{n+k-1}$, so $\beta_k = 0$, $\beta_j = \frac1h \int_{x_{n+k-1}}^{x_{n+k}} L_j(x)\,dx$ for the Lagrange basis $L_j$ of those nodes, and it is explicit;
- the $k$-step Adams–Moulton method interpolates at the $k + 1$ nodes $x_n, \dots, x_{n+k}$, the new endpoint included, with $\beta_j$ defined in the same way, and it is implicit.

With these coefficients the $k$-step Adams–Bashforth method has [order](../order-of-accuracy-and-error-constants.md) $k$ and the $k$-step Adams–Moulton method order $k + 1$; for $k = 2$,

$$y_{n+2} - y_{n+1} = \tfrac{h}{2}(3 f_{n+1} - f_n) \qquad\text{and}\qquad y_{n+2} - y_{n+1} = \tfrac{h}{12}(5 f_{n+2} + 8 f_{n+1} - f_n).$$

The orders are properties of these coefficients, not of $\rho$ alone: backward Euler, $y_{n+1} - y_n = h f_{n+1}$, is an implicit Adams method with $k = 1$ but has order one.

## Depends on

- [Linear multistep method](../linear-multistep-method.md)
- [Order of accuracy and error constants of a linear multistep method](../order-of-accuracy-and-error-constants.md)
- [Zero-stability](../zero-stability.md)
- [Evaluated Lagrange basis polynomial](../../../approximation-theory/lagrange-interpolation/eval-basis.md)

## Proof depends on

- [Zero-stability and the root condition](../zero-stability-iff-root-condition.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.1, the integral form $y(x_{n+1}) - y(x_n) = \int_{x_n}^{x_{n+1}} y'(\xi)\,d\xi$, the backward-difference expansions (41)–(42) and their truncations, which give the Adams–Moulton and Adams–Bashforth formulas (the truncated backward-difference form of the interpolant integrals above); Example 4(b); the end of Section 3.5, the broad terminology (every method with $\rho(z) = z^k - z^{k-1}$ is an Adams method, explicit ones Adams–Bashforth, implicit ones Adams–Moulton); Section 3.7.2, the particular $k$-step Adams methods for $k \le 4$ with their orders. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
