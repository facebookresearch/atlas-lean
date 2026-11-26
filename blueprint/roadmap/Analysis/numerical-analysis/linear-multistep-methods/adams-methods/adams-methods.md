# Adams methods

A [linear $k$-step method](../linear-multistep-method.md) whose first characteristic polynomial is

$$\rho(z) = z^k - z^{k-1}$$

is an *Adams method*: it advances $y_{n+k} = y_{n+k-1} + h \sum_{j=0}^{k} \beta_j f_{n+j}$, approximating $\int_{x_{n+k-1}}^{x_{n+k}} y'$ by integrating a polynomial interpolant of past values of $f$. The explicit ones ($\beta_k = 0$) are the *Adams–Bashforth* methods and the implicit ones the *Adams–Moulton* methods. The $k$-step Adams–Bashforth method has order $k$, the $k$-step Adams–Moulton method order $k + 1$; for $k = 2$,

$$y_{n+2} - y_{n+1} = \tfrac{h}{2}(3 f_{n+1} - f_n) \qquad\text{and}\qquad y_{n+2} - y_{n+1} = \tfrac{h}{12}(5 f_{n+2} + 8 f_{n+1} - f_n).$$

Since the roots of $\rho$ are $1$ and $0$, every Adams method is zero-stable.

## Depends on

- [Linear multistep method](../linear-multistep-method.md)
- [Order of accuracy and error constants of a linear multistep method](../order-of-accuracy-and-error-constants.md)
- [Zero-stability](../zero-stability.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.1, the expansions (41)–(42) and their truncations; Example 4(b); the end of Section 3.5, the definition of Adams, Adams–Bashforth and Adams–Moulton methods by $\rho(z) = z^k - z^{k-1}$; Section 3.7.2, the list of $k$-step Adams methods for $k \le 4$. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
