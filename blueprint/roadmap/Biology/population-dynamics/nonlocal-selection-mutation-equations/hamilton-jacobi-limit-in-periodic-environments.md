# Hamilton–Jacobi limit of periodic selection–mutation equations

Under the assumptions of [selection of the time-averaged fittest trait](selection-of-the-time-averaged-fittest-trait.md) (periodic, bounded $a$; unique maximizer $x_m$ of $\bar a$ with $\bar a(x_m) > 0$; $a + \lambda \le -\delta$ at infinity), let $(n_\varepsilon, \rho_\varepsilon)$ be the unique positive $T$-periodic solution of

$$\partial_t n_\varepsilon - \varepsilon^2\Delta n_\varepsilon = n_\varepsilon\,[a(t,x) - \rho_\varepsilon(t)], \qquad \rho_\varepsilon(t) = \int n_\varepsilon(t,x)\,dx,$$

and write $n_\varepsilon = (2\pi\varepsilon)^{-d/2}\exp(u_\varepsilon/\varepsilon)$ (Hopf–Cole transformation).

**Theorem.** As $\varepsilon \to 0$:
1. $\|\rho_\varepsilon - \tilde\varrho\|_{L^\infty} \to 0$ and $n_\varepsilon(t,\cdot) - \tilde\varrho(t)\,\delta_{x_m} \rightharpoonup 0$ weakly as measures, pointwise in $t$, where $\tilde\varrho$ is the positive periodic solution of $\tilde\varrho' = \tilde\varrho\,(a(t,x_m) - \tilde\varrho)$;
2. $u_\varepsilon \to u$ locally uniformly, where $u$ is time-independent and is the unique viscosity solution of the Hamilton–Jacobi equation with constraint

$$-|\nabla u(x)|^2 = \frac1T\int_0^T\bigl(a(t,x) - \tilde\varrho(t)\bigr)\,dt = \bar a(x) - \bar\varrho, \qquad \max_{x}u(x) = u(x_m) = 0,$$

with $\bar\varrho = \frac1T\int_0^T\tilde\varrho\,dt = \bar a(x_m)$.

In dimension $d = 1$ the solution is classical:

$$u(x) = -\left|\int_{x_m}^{x}\sqrt{\bar\varrho - \bar a(y)}\,dy\right|.$$

## Depends on

- [Selection of the trait with the largest time-averaged growth rate](selection-of-the-time-averaged-fittest-trait.md)
- [Periodic logistic equation](periodic-logistic-equation.md)
- [Viscosity solution of a first-order equation](../../../Analysis/partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/is-viscosity-solution.md)

## Proof depends on

- [Stability of viscosity solutions under locally uniform limits](../../../Analysis/partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/solution-of-tendsto-locally-uniformly-on.md)
- [Classical solutions are viscosity solutions](../../../Analysis/partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/is-viscosity-solution-of-classical.md)

## Expansion

The transformed function solves $\frac1\varepsilon\partial_t u_\varepsilon - \varepsilon\Delta u_\varepsilon = |\nabla u_\varepsilon|^2 + a(t,x) - \rho_\varepsilon(t)$. Substituting $u_\varepsilon = u + \varepsilon v + \varepsilon^2 w + \cdots$ and $\rho_\varepsilon = \rho + \varepsilon\kappa + \cdots$ with periodic coefficients, the order $\varepsilon^{-1}$ terms give $\partial_t u = 0$, and the order-one terms give $\partial_t v = |\nabla u|^2 + a - \rho$; integrating over a period and using periodicity of $v$ yields the Hamilton–Jacobi equation, whose right side is the time-averaged growth rate. The constraint $\max u = 0$ expresses that $\rho_\varepsilon$ stays bounded away from $0$ and $\infty$, and $n_\varepsilon$ concentrates on the zero set of $u$, which is $\{x_m\}$. The rigorous proof derives regularity estimates on $u_\varepsilon$ despite its periodicity in time and passes to the limit with perturbed test functions; the next-order terms give Laplace-method approximations of the trait mean and variance when $\varepsilon$ is small but positive.

## Sources

- S. Figueroa Iglesias and S. Mirrahimi, "Long time evolutionary dynamics of phenotypically structured populations in time-periodic environments", SIAM Journal on Mathematical Analysis (2018), Section 1.3 (Proposition 1, Equations 3–4; Proposition 2, Equations 5–8; Theorem 4, Equations 9–13), Section 1.4 (Equations 14–16) and Section 2, <https://doi.org/10.1137/18M1175185>.
