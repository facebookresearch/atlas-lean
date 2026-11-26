# Late-time asymptotics of the Michaelis–Menten Selkov system

Let $\gamma > 1$, $\alpha, \beta > 0$ and $0 < \nu < 1$. The **Michaelis–Menten Selkov system**, the quasi-steady-state reduction from which the basic Selkov system is the limit $\nu \to 0$, is

$$\frac{dx}{d\tau} = 1 - \frac{x y^{\gamma}}{1 + \nu y^{\gamma}(\beta + x)}, \qquad \frac{dy}{d\tau} = \alpha\left[\frac{x y^{\gamma}}{1 + \nu y^{\gamma}(\beta + x)} - y\right].$$

**Theorem (escape asymptotics).** There is $\epsilon > 0$ such that every solution with $x(0) > \epsilon^{-1}$ and $x(0)\,y(0)^{\gamma} < \epsilon$ satisfies, for some constant $y_1$,

$$x(\tau) = \tau\,(1 + o(1)), \qquad y(\tau) = y_1 e^{-\alpha\tau}(1 + o(1)) \quad (\tau \to \infty),$$

and there is a solution, unique up to time translation, with $x(\tau) = \tau(1+o(1))$ and $y(\tau) = \tau^{-1/(\gamma-1)}(1+o(1))$. The leading-order asymptotics do not depend on $\nu$.

**Theorem (global properties).**
1. The unique positive steady state is $\bigl(\tfrac{1+\beta\nu}{1-\nu},\,1\bigr)$.
2. If $\gamma \le \tfrac{1+\beta\nu}{1-\nu}$ it is stable; otherwise it is stable for $\alpha < \alpha_0 := \dfrac{(1-\nu)^2}{\gamma(1-\nu) - (1+\beta\nu)}$ and unstable for $\alpha > \alpha_0$.
3. At $\alpha = \alpha_0$ a Hopf bifurcation occurs, and parameters can be chosen to make it either supercritical or subcritical; in the subcritical case there are unstable periodic solutions, which never occur in the basic Selkov system.
4. For all $(\alpha,\nu)$ there are $x_0, y_0 > 0$ such that any solution with $x \ge x_0$, $y \le y_0$ at some time has the escape asymptotics above.
5. For $\gamma = 2$ there are positive $(\alpha,\nu)$ for which every solution other than the steady state has these asymptotics.

## Expansion

Setting $\nu = 0$ recovers the basic system and its steady state $(1,1)$ and threshold $\alpha_0 = 1/(\gamma-1)$. The Poincaré compactification with variables $Y = y/x$, $Z = 1/x$ produces boundary steady states, one of which ($P_8$) attracts all solutions starting near it; integrating the compactified equations to leading order and transforming back gives the linear growth of $x$ and exponential decay of $y$. The second solution lies on the centre manifold of another boundary point ($P_7$). Part 5 comes from the same geometric singular perturbation argument as for the basic system, letting $\epsilon = \alpha^{-1}$ and $\nu = \epsilon^2$ tend to zero together, which produces a heteroclinic orbit from the positive steady state to $P_7$ and so rules out periodic orbits. Whether unbounded oscillations exist when $\nu > 0$ is left open.

## Depends on

- [Unbounded oscillations of the basic Selkov system](unbounded-oscillations-of-the-basic-selkov-system.md)

## Sources

- P. Brechmann, A. D. Rendall, "Unbounded solutions of models for glycolysis", Journal of Mathematical Biology (2021), Eqs. (7)–(8), Theorem 3, Lemmas 5–9 and Theorem 4, <https://doi.org/10.1007/s00285-021-01560-y>, PMCID PMC7819955.
