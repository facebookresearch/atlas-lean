# Bang-bang optimal quarantine with a strict-phase time budget

**Model.** Let $x, y$ be the susceptible and infected fractions of an SIR epidemic with recovery rate $\gamma > 0$ and a controlled reproduction number $\sigma(t)$:

$$
x' = -\gamma \sigma(t)\, x y, \qquad y' = \gamma \sigma(t)\, x y - \gamma y, \qquad (x(0), y(0)) = (x_0, y_0),\ x_0 > 0,\ y_0 > 0,\ x_0 + y_0 \le 1 .
$$

On the intervention window $[0, T]$ the control is a measurable $\sigma : [0, T] \to [\sigma_s, \sigma_m]$, where $\sigma_s$ is a strict quarantine and $\sigma_m$ a mild one; after $T$ restrictions are lifted and $\sigma \equiv \sigma_f$, with $0 \le \sigma_s < \sigma_m \le \sigma_f$. The strict level may be used for at most a fixed time $\tau \in (0, T)$, imposed through the budget

$$
\int_0^T \sigma(t)\, dt \ \ge\ \sigma_s \tau + \sigma_m (T - \tau),
$$

which forces $\lvert\{t : \sigma(t) = \sigma_s\}\rvert \le \tau$. Let $x_\infty(x, y, \sigma_f) = -\sigma_f^{-1} W_0\big(-\sigma_f\, x\, e^{-\sigma_f (x + y)}\big)$ be the eventual susceptible fraction of the uncontrolled flow started at $(x, y)$, with $W_0$ the principal branch of the Lambert $W$ function. For a cost weight $\kappa \ge 0$ the objective is

$$
\max_{\sigma}\ J(\sigma) = x_\infty\big(x(T), y(T), \sigma_f\big) + \kappa \int_0^T \sigma(t)\, dt .
$$

**Theorem.**

1. An optimal control exists.
2. The problem is normal (the cost multiplier in Pontryagin's principle can be taken equal to $1$), and every optimal control is bang-bang: there are no singular arcs, and $\sigma^*(t) = \sigma_m$ where the switching function

    $$
    \phi(t) = \kappa + \beta + \gamma\, x^*(t)\, y^*(t)\, \big(\lambda_2(t) - \lambda_1(t)\big)
    $$

    is positive and $\sigma^*(t) = \sigma_s$ where it is negative. Here $\beta \ge 0$ is the constant multiplier of the budget constraint and $(\lambda_1, \lambda_2)$ solve

    $$
    \lambda_1' = (\lambda_1 - \lambda_2)\, \gamma \sigma y, \qquad \lambda_2' = (\lambda_1 - \lambda_2)\, \gamma \sigma x + \gamma \lambda_2,
    $$

    with terminal values given by the partial derivatives of the final size,

    $$
    \lambda_1(T) = \frac{\partial x_\infty}{\partial x(T)} = \frac{1 - \sigma_f x(T)}{x(T)} \cdot \frac{x_\infty}{1 - \sigma_f x_\infty}, \qquad \lambda_2(T) = \frac{\partial x_\infty}{\partial y(T)} = -\frac{\sigma_f x_\infty}{1 - \sigma_f x_\infty} < 0 .
    $$

3. $\phi$ changes sign at most twice on $[0, T]$.
4. Consequently every optimal control is mild, then strict, then mild:

    $$
    \sigma^*(t) = \begin{cases} \sigma_m, & 0 \le t < t_1, \\ \sigma_s, & t_1 \le t < t_1 + \eta, \\ \sigma_m, & t_1 + \eta \le t \le T, \end{cases} \qquad 0 \le \eta \le \tau,
    $$

    so the strict quarantine is switched on at most once, and the problem reduces to maximizing a function of the two numbers $(t_1, \eta)$ over $\{0 \le \eta \le \tau,\ 0 \le t_1 \le T - \eta\}$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)
- [Limits and final size of the SIR epidemic](../../global-behaviour-of-the-sir-model/tendsto-final-size.md)

## Expansion

For constant $\sigma$ the quantity $x e^{-\sigma(x + y)}$ is conserved, and since $y \to 0$ the final size satisfies $x_\infty e^{-\sigma x_\infty} = x e^{-\sigma(x+y)}$, which the Lambert $W$ function inverts. Adding the state $v(t) = \int_0^t \sigma$ turns the budget into the terminal constraint $v(T) \ge \sigma_m T + (\sigma_s - \sigma_m)\tau$; existence follows from a Filippov-type theorem because the running cost $\kappa\sigma$ is continuous and convex and the controlled vector field is affine in $\sigma$. If the cost multiplier vanished, the adjoints would vanish identically, $\phi \equiv \beta > 0$, and the control would be $\sigma_m$ throughout, contradicting the complementary slackness that forces the budget to be active. On a singular arc $\phi' = \gamma x y \lambda_1 = 0$ would give $\lambda_1 = \lambda_2 = 0$ on an interval and then everywhere, contradicting the terminal values. The sign-change bound comes from a phase-plane analysis of $(\lambda_1, \lambda_2)$ run backwards from the terminal point, which the source places in the quadrant $\lambda_1 > 0 > \lambda_2$ (by the formula above, $\lambda_1(T) > 0$ holds when $\sigma_f x(T) < 1$): the constant Hamiltonian prevents the adjoint path from crossing both half-lines $\lambda_1 = \lambda_2 > 0$ and $\lambda_1 = \lambda_2 < 0$, and $\phi$ can be negative only while $\lambda_1 > \lambda_2$, where it first decreases and then increases. Combined with the budget, at most two switches means a single strict interval of length at most $\tau$.

## Sources

- R. Balderrama, J. Peressutti, J. P. Pinasco, F. Vazquez, C. Sánchez de la Vega, "Optimal control for a SIR epidemic model with limited quarantine", Scientific Reports 12 (2022), 12583; Methods section, problem (16), Eqs. (15) and (17) to (25), Proposition 1, Lemmas 1 to 4 and Theorem 1. <https://doi.org/10.1038/s41598-022-16619-z> (PMCID: PMC9307862).
