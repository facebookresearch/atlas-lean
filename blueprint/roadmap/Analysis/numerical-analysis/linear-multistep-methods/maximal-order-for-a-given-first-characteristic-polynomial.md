# Maximal order for a given first characteristic polynomial

Let $\rho$ be a real polynomial of degree $k \ge 1$ with $\rho(1) = 0$ and $\rho'(1) \ne 0$, and let $\hat k$ be an integer with $0 \le \hat k \le k$. Then there is a unique real polynomial $\sigma$ of degree at most $\hat k$ such that $\sigma(1) = \rho'(1)$ and the coefficient pair $(\rho, \sigma)$ satisfies the [order conditions](order-conditions.md) up to order $\hat k + 1$. It defines a [linear $k$-step method](linear-multistep-method.md), of [order of accuracy](order-of-accuracy-and-error-constants.md) at least $\hat k + 1$, when the constant coefficients $\alpha_0$ and $\beta_0$ do not both vanish.

Explicitly, if $\rho(z)/\log z = c_0 + c_1(z - 1) + c_2(z - 1)^2 + \cdots$ near $z = 1$, then $\sigma(z) = c_0 + c_1(z - 1) + \cdots + c_{\hat k}(z - 1)^{\hat k}$. The choice $\hat k = k - 1$ gives an explicit method when the pair defines a method. The choice $\hat k = k$ gives an implicit one only when the coefficient of $z^k$ in $\sigma$ is nonzero: for $\rho(z) = z^2 + 4z - 5$ it gives $\sigma(z) = 2 + 4z$, an explicit method of order $3$. For $\rho(z) = z^2 - 1$ and $\hat k = 2$ it is Simpson's method $y_{n+2} - y_n = \tfrac{h}{3}(f_{n+2} + 4f_{n+1} + f_n)$, of order $4$; for $\rho(z) = z(z^2 - 1)$ and $\hat k = 3$ the same method shifted by one step comes out, with $\alpha_0 = \beta_0 = 0$, which is not a three-step method.

## Depends on

- [Linear multistep method](linear-multistep-method.md)
- [Order of accuracy and error constants of a linear multistep method](order-of-accuracy-and-error-constants.md)

## Proof depends on

- [Order conditions for linear multistep methods](order-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.5, Theorem 11 and its proof (via Lemma 3), and Example 5 (the case $\lambda = -1$ gives Simpson's method). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
