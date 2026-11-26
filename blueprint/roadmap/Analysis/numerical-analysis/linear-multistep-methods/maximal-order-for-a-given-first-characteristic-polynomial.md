# Maximal order for a given first characteristic polynomial

Let $\rho$ be a real polynomial of degree $k \ge 1$ with $\rho(1) = 0$ and $\rho'(1) \ne 0$, and let $\hat k$ be an integer with $0 \le \hat k \le k$. Then there is a unique real polynomial $\sigma$ of degree at most $\hat k$ such that $\sigma(1) = \rho'(1)$ and the [linear multistep method](linear-multistep-method.md) with characteristic polynomials $\rho$ and $\sigma$ has [order of accuracy](order-of-accuracy-and-error-constants.md) at least $\hat k + 1$.

Explicitly, if $\rho(z)/\log z = c_0 + c_1(z - 1) + c_2(z - 1)^2 + \cdots$ near $z = 1$, then $\sigma(z) = c_0 + c_1(z - 1) + \cdots + c_{\hat k}(z - 1)^{\hat k}$. The choices $\hat k = k - 1$ and $\hat k = k$ give explicit and implicit methods; for $\rho(z) = z^2 - 1$ and $\hat k = 2$ this is Simpson's method $y_{n+2} - y_n = \tfrac{h}{3}(f_{n+2} + 4f_{n+1} + f_n)$, of order $4$.

## Depends on

- [Linear multistep method](linear-multistep-method.md)
- [Order of accuracy and error constants of a linear multistep method](order-of-accuracy-and-error-constants.md)

## Proof depends on

- [Order conditions for linear multistep methods](order-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.5, Theorem 11 and its proof (via Lemma 3), and Example 5 (the case $\lambda = -1$ gives Simpson's method). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
