# Single-peak dynamics of SIR epidemics with state-dependent contact rates

On the simplex $\mathcal S = \{(x,y,z) \in [0,1]^3 : x + y + z = 1\}$ of susceptible, infected and recovered fractions consider

$$\dot x = -x\,y\,f(x,y), \qquad \dot y = x\,y\,f(x,y) - \gamma y, \qquad \dot z = \gamma y,$$

with recovery rate $\gamma > 0$ and a contact rate $f \ge 0$ of class $C^1$ that may depend on the epidemic state (behavioral response or policy). Define the effective reproduction number

$$R(t) = \frac{x(t)\, f(x(t), y(t))}{\gamma}.$$

**Theorem.** Assume $\partial f/\partial x \ge 0$ on $\mathcal S$. Then:

1. If $R(0) < 1$, then $R(t) < 1$ for all $t \ge 0$, and $y(t)$ decreases monotonically to $0$.
2. If $R(0) > 1$ and $y(0) > 0$, there is $t^* > 0$ such that $y$ is increasing on $[0,t^*]$ and decreasing on $[t^*,\infty)$ with $y(t) \to 0$.

So any contact-rate feedback that does not increase contacts as susceptibles are depleted keeps the classical single-wave behaviour; multiple waves require $f$ to increase as $x$ decreases. For constant $f = \beta$ this is the classical result, with peak $y^{\max} = M(\epsilon,\rho) = 1 - \rho + \rho\ln\rho - \rho\ln(1-\epsilon)$ from initial data $(1-\epsilon,\epsilon,0)$ and $\rho = \gamma/\beta < 1 - \epsilon$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

$\dot y = \gamma y\,(R - 1)$, so the sign of $\dot y$ is the sign of $R - 1$. If $R$ first returned to $1$ at a time $t^*$ from below, then $\dot R(t^*) \ge 0$; but $\gamma\dot R = \dot x\,(f + x\,\partial_x f) + x\,\partial_y f\,\dot y$, and at $t^*$ the last term vanishes because $\dot y(t^*) = 0$, while $\dot x < 0$ and $f + x\partial_x f > 0$ make the first term negative, a contradiction. Since $x$ is decreasing and bounded, $\int_0^\infty x y f\,dt < \infty$, which forces $y \to 0$; when $R(0) > 1$ the same invariance argument applied after the first time $R$ hits $1$ gives a single peak.

## Sources

- Martina Alutto, Giacomo Como, Fabio Fagnani, "On SIR epidemic models with feedback-controlled interactions and network effects", in 2021 60th IEEE Conference on Decision and Control (CDC) (2021), 5562–5567, <https://doi.org/10.1109/cdc45484.2021.9683007>. Published version of arXiv:2105.01538, cited next; locators there refer to the arXiv version.
- Martina Alutto, Giacomo Como, Fabio Fagnani, "On SIR epidemic models with feedback-controlled interactions and network effects", arXiv (2021). Section 2, Proposition 1, Theorem 1, Remark 1. <https://doi.org/10.48550/arXiv.2105.01538>
