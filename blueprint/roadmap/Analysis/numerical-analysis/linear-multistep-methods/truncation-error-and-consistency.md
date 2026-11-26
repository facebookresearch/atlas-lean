# Truncation error and consistency of a linear multistep method

Let a [linear $k$-step method](linear-multistep-method.md) have characteristic polynomials $\rho$ and $\sigma$ with $\sigma(1) = \sum_{j=0}^{k} \beta_j \ne 0$, and let $y$ be a solution of $y' = f(x, y)$. The *truncation error* of the method at $x_n$ with step $h$ is

$$T_n = \frac{\sum_{j=0}^{k} \bigl[\alpha_j\, y(x_{n+j}) - h \beta_j\, y'(x_{n+j})\bigr]}{h\, \sigma(1)},$$

the residual left when the exact solution is inserted into the method, scaled so that it resembles $y' - f(x, y(x))$.

The method is *consistent* with the differential equation if for every $\varepsilon > 0$ there is $h(\varepsilon) > 0$ such that $|T_n| < \varepsilon$ for every $0 < h < h(\varepsilon)$ and every $k + 1$ consecutive mesh points $(x_n, y(x_n)), \dots, (x_{n+k}, y(x_{n+k}))$ on any solution curve of the initial value problem in the rectangle $R = \{(x, y) : x_0 \le x \le X_M,\ |y - y_0| \le Y_M\}$.

## Depends on

- [Linear multistep method](linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.3, equation (46) and Definition 5. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
