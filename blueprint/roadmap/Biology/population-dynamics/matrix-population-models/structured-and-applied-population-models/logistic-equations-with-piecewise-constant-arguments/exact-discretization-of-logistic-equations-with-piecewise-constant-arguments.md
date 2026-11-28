# Exact discretization of logistic equations with piecewise constant arguments

**Setting.** Population models with piecewise constant arguments freeze the interaction terms at the last integer time: for a vector of densities $y(t) = (y_1, \dots, y_k)$ each component obeys, on every interval $n \le t < n+1$,

$$x'(t) = x(t)\big(A(y(n)) - b\, x(t)\big), \qquad b > 0,$$

where $x = y_i$ and $A$ is a given function (intrinsic growth plus interaction terms evaluated at $t = n$). Write $A_n = A(y(n))$.

**Proposition (exact one-step map).** For $x(n) > 0$ the solution on $[n, n+1)$ is positive, and at $t = n+1$

$$x(n+1) = \frac{A_n\, x(n)}{b\, x(n) + \big(A_n - b\, x(n)\big) e^{-A_n}} \qquad (A_n \ne 0),$$

with the limit $x(n+1) = x(n)/(1 + b\,x(n))$ when $A_n = 0$. Hence the continuous-time system is equivalent to an explicit system of difference equations whose global behavior is that of the original model at integer times.

**Proposition (diagonal multiplier).** If $A$ does not depend on $x$ and $A > 0$, the one-dimensional map $f(x) = A x / (b x + (A - bx) e^{-A})$ has the positive fixed point $x^* = A/b$ with $f'(x^*) = e^{-A} \in (0,1)$, so $x^*$ is locally asymptotically stable. In a coupled system, at a positive equilibrium with $x^* = \bar A/b$, $\bar A$ the frozen growth term evaluated there, the diagonal Jacobian entry of the component $x$ is
$$\frac{\partial x(n+1)}{\partial x(n)} = e^{-\bar A} + \frac{\partial A}{\partial x}\,\frac{1 - e^{-\bar A}}{b},$$
which is $e^{-\bar A}$ exactly when the frozen term does not depend on $x$ itself.

**Lemma (second-order Schur–Cohn test).** The roots of $\lambda^2 - p\lambda - q = 0$ with real $p, q$ satisfy $|\lambda_{1,2}| < 1$ if and only if

$$|p| < 1 - q < 2 .$$

For a Jacobian with block-triangular structure the characteristic polynomial factors into such quadratics and linear factors, and the test is applied block by block.

## Depends on

- [Explicit solution of the logistic equation](../../../logistic-growth-equation/logistic.md)

## Expansion

On $[n, n+1)$ the equation is a Bernoulli equation. Setting $u = 1/x$ gives the linear equation $u' = -A_n u + b$, so $u(t) = b/A_n + (u(n) - b/A_n) e^{-A_n (t-n)}$, which stays positive when $u(n) > 0$; inverting at $t = n + 1$ gives the map. Differentiating $f$ and substituting $b x^* = A$ makes the denominator equal $A$ and leaves $f'(x^*) = e^{-A}$. The quadratic test follows from the Jury conditions $1 - p - q > 0$, $1 + p - q > 0$, $|q| < 1$ for $\lambda^2 - p \lambda - q$. These facts are the backbone of the local and global stability analysis of a five-class bat, intermediate host and human coronavirus spillover model with piecewise constant arguments.

## Sources

- F. Bozkurt, A. Yousef, D. Baleanu, J. Alzabut, "A mathematical model of the evolution and spread of pathogenic coronaviruses from natural host to human host", Chaos, Solitons and Fractals 138 (2020) 109931, Section 3, Equations (3)-(8) and Theorem 1, <https://doi.org/10.1016/j.chaos.2020.109931>, PMCID PMC7280153.
