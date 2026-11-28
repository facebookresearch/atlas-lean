# Global behavior of the diffusive SIR model with power-saturated incidence

**ODE model.** Let $\tau,\kappa,\lambda,p,q > 0$ with $1 \le p \le q + 1$ and $S_0, I_0 > 0$. The system

$$S' = -\frac{\tau I^p}{1 + \kappa I^q}\,S, \qquad I' = \frac{\tau I^p}{1 + \kappa I^q}\,S - \lambda I$$

has a unique global solution with $S, I \ge 0$. With

$$R_0 = \frac{\tau I_0^{p-1} S_0}{\lambda(1 + \kappa I_0^q)},$$

if $R_0 < 1$ then $S$ decreases to $S_\infty > 0$ and $I$ decreases to $0$; if $R_0 > 1$ then $S$ decreases to $S_\infty > 0$ while $I$ first increases and then decreases to $0$.

**PDE model.** Let $\Omega \subset \mathbb R^n$ be bounded with smooth boundary, $\alpha,\tau,\kappa,p,q > 0$ with $1 \le p \le q+1$, a spatially varying recovery rate $\lambda \in C_+(\overline\Omega)$ with $\lambda \ge \lambda_0 > 0$, and nontrivial $S_0, I_0 \in L^1_+(\Omega)$. Then there is a unique global solution $S, I : [0,\infty) \to L^1_+(\Omega)$ of

$$\partial_t S = -\frac{\tau I^p}{1 + \kappa I^q}\,S, \qquad \partial_t I = \alpha\Delta I + \frac{\tau I^p}{1 + \kappa I^q}\,S - \lambda(x)I, \qquad \partial_\eta I = 0 \text{ on } \partial\Omega,$$

and, in $L^1(\Omega)$,

$$\lim_{t\to\infty} S(t,\cdot) = S_\infty \ge 0, \quad S_\infty \ne 0, \qquad \lim_{t\to\infty} I(t,\cdot) = 0.$$

The constraint $p \le q + 1$ keeps the incidence per infective $\tau I^{p-1}S/(1+\kappa I^q)$ bounded in $I$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

In the ODE, $S$ is decreasing and bounded below, and integrating $S'/S$ gives $\ln(S_0/S_\infty) = \int_0^\infty \tau I^p/(1+\kappa I^q)\,dt$, which is finite because $p \ge 1$ makes the integrand at most a constant times $I$ and $\int_0^\infty I\,dt \le (S_0 + I_0)/\lambda$ from $(S+I)' = -\lambda I$; hence $S_\infty > 0$ and $I \to 0$. The sign of $I'$ is governed by $\tau I^{p-1}S/(1+\kappa I^q) - \lambda$, whose initial value has the sign of $R_0 - 1$. For the PDE, $S$ solves an ODE at each point and is decreasing; $\int_\Omega(S + I)$ is nonincreasing with derivative $-\int_\Omega\lambda I \le -\lambda_0\int_\Omega I$, which bounds $\int_0^\infty\|I\|_{L^1}dt$ and gives $I \to 0$ and a nonzero limit of $S$.

## Sources

- Pierre Magal, Glenn F. Webb, Yixiang Wu, "Spatial spread of epidemic diseases in geographical settings: Seasonal influenza epidemics in Puerto Rico", Discrete and Continuous Dynamical Systems - B 25 (2020), 2185–2202, <https://doi.org/10.3934/dcdsb.2019223>. Published version of arXiv:1801.01856, cited next; locators there refer to the arXiv version.
- Pierre Magal, Glenn F. Webb, Yixiang Wu, "Spatial Spread of Epidemic Diseases in Geographical Settings: Seasonal Influenza Epidemics in Puerto Rico", arXiv (2018). Theorem 4.1, Theorem 4.4. <https://doi.org/10.48550/arXiv.1801.01856>
