# Truncation error and consistency of a linear multistep method

Let a [linear $k$-step method](linear-multistep-method.md) have characteristic polynomials $\rho$ and $\sigma$ with $\sigma(1) = \sum_{j=0}^{k} \beta_j \ne 0$, and let $y$ be a solution of $y' = f(x, y)$. The *truncation error* of the method at $x_n$ with step $h$ is

$$T_n = \frac{\sum_{j=0}^{k} \bigl[\alpha_j\, y(x_{n+j}) - h \beta_j\, y'(x_{n+j})\bigr]}{h\, \sigma(1)},$$

the residual left when the exact solution is inserted into the method, scaled so that it resembles $y' - f(x, y(x))$.

The method is *consistent with a given initial value problem* $y' = f(x, y)$, $y(x_0) = y_0$ on $[x_0, X_M]$, with solution $y$, if for every $\varepsilon > 0$ there is $h(\varepsilon) > 0$ such that $|T_n| < \varepsilon$ for every $0 < h < h(\varepsilon)$ and every $n$ with $x_{n+k} \le X_M$. The *method* is *consistent* if it is consistent with every initial value problem $y' = f(x, y)$, $y(x_0) = y_0$ on $[x_0, X_M]$ whose right-hand side $f$ is continuous on $[x_0, X_M] \times \mathbb{R}$ and Lipschitz in $y$.

Consistency with one problem says little about the method: for $y' = 0$, $y(0) = 0$, whose solution is $0$, every method has $T_n = 0$, including $y_{n+1} + y_n = h f(x_n, y_n)$, which is not consistent.

## Depends on

- [Linear multistep method](linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.3, equation (46) and Definition 5. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
- G. Dahlquist, "33 years of numerical instability, Part I", *BIT* 25 (1985), 188–204, Section 3, the local truncation error $L_h y(t)$ of (3.3), defined for arbitrary sufficiently regular functions $y$, and the order of consistency defined from it. <https://doi.org/10.1007/BF01934997>
