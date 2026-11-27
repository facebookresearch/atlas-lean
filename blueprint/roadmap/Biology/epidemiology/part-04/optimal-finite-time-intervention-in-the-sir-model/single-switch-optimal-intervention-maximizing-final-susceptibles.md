# Single-switch optimal intervention maximizing final susceptibles

**Model.** Susceptible and infected fractions $x, y$ follow the SIR model with a controlled reproduction number $\sigma(t) \in [0, \sigma_0]$ on a finite window $[0, T]$ and $\sigma = \sigma_0$ afterwards:

$$x' = -\gamma\sigma(t)\, x y, \qquad y' = \gamma\sigma(t)\, x y - \gamma y, \qquad (x_0, y_0) \in \{x_0 > 0,\ y_0 > 0,\ x_0 + y_0 \le 1\},$$

with recovery rate $\gamma > 0$ and basic reproduction number $\sigma_0 > 0$. The goal is to maximize the final susceptible fraction $x_\infty = \lim_{t\to\infty} x(t)$, i.e. to minimize the eventual number ever infected.

**Final size from any state.** For the uncontrolled flow, $\mu(x, y) = x\, e^{-\sigma_0(x + y)}$ is a first integral, and the eventual susceptible fraction from state $(x, y)$ is

$$x_\infty(x, y) = -\frac{1}{\sigma_0} W_0\big(-\sigma_0\, \mu(x, y)\big),$$

with $W_0$ the principal branch of the Lambert $W$ function; it increases with $\mu$, and along a controlled trajectory

$$\frac{d}{dt}\, x_\infty\big(x(t), y(t)\big) = \frac{\gamma\, y\, x_\infty}{1 - \sigma_0 x_\infty}\,\big(\sigma_0 - \sigma(t)\big) \ \ge 0 .$$

Hence every admissible control weakly increases $x_\infty$, and $x_\infty(x_0, y_0) \le x_\infty(x(T), y(T)) \le 1/\sigma_0$.

**Theorem.** With no running cost, the problem of maximizing $x_\infty(x(T), y(T))$ over measurable $\sigma : [0,T] \to [0, \sigma_0]$ has a unique solution, the single-switch bang–bang control

$$\sigma^\ast(t) = \begin{cases} \sigma_0, & t < t^\ast,\\ 0, & t^\ast < t \le T, \end{cases}$$

where $t^\ast = 0$ if $x_0 \le \dfrac{1}{\sigma_0(1 - e^{-\gamma T})}$, and otherwise $t^\ast \in (0, T)$ is the unique solution of

$$x(t^\ast; \sigma_0, x_0, y_0) = \frac{1}{\sigma_0\big(1 - e^{-\gamma(T - t^\ast)}\big)} .$$

That is, the epidemic runs uncontrolled until the susceptible fraction falls to this moving threshold, and the strongest intervention is applied for the rest of the window.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)
- [Limits and final size of the SIR epidemic](../../global-behaviour-of-the-sir-model/tendsto-final-size.md)

## Expansion

Since $\mu' = \gamma y(\sigma_0 - \sigma)\mu$, maximizing $x_\infty$ is equivalent to maximizing $I = \int_0^T y(\tau)(\sigma_0 - \sigma(\tau))\, d\tau$. Pontryagin's principle with Hamiltonian $H = -\lambda_1\gamma\sigma x y + \lambda_2\gamma y(\sigma x - 1)$ gives $\partial H/\partial\sigma = (\lambda_2 - \lambda_1)\gamma x y$, so optimal controls are bang–bang; a singular arc would force $\lambda_1 = \lambda_2$ on all of $[0,T]$, contradicting the terminal conditions derived from the partial derivatives of $x_\infty$. An optimal control must also reach its terminal state in minimum time, and among bang–bang paths between two states the fastest makes all its horizontal ($\sigma = \sigma_0$) and vertical ($\sigma = 0$) travel at the largest possible $y$, which forces a single switch from $\sigma_0$ to $0$. For such a control $I = \frac{\sigma_0}{\gamma}\, y(t^\ast)\big(1 - e^{-\gamma(T - t^\ast)}\big)$, and $dI/dt^\ast = \sigma_0 y(t^\ast)\big[\sigma_0 x(t^\ast)(1 - e^{-\gamma(T - t^\ast)}) - 1\big]$ vanishes exactly at the stated threshold. The result is not obtained from standard Pontryagin sufficiency conditions because the SIR right-hand side is nonconvex; with a running cost of control the optimum becomes continuous and is computed numerically.

## Sources

- D. I. Ketcheson, "Optimal control of an SIR epidemic through finite-time non-pharmaceutical intervention", Journal of Mathematical Biology 83 (2021), 7, Sections 2–3 (Eqs. (1)–(23), Lemmas 1–4, Theorems 1–3), <https://doi.org/10.1007/s00285-021-01628-9>, PMCID: PMC8235921.
