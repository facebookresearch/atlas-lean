# Optimal onset of a budget-limited strict quarantine in the SIR model

**Setting.** Use the SIR control problem with a strict-phase time budget: $x' = -\gamma\sigma x y$, $y' = \gamma\sigma x y - \gamma y$ from $(x_0, y_0)$ with $x_0, y_0 > 0$, $x_0 + y_0 \le 1$; control $\sigma(t) \in [\sigma_s, \sigma_m]$ on $[0, T]$, strict level $\sigma_s$ used for at most $\tau \in (0, T)$, $\sigma \equiv \sigma_f$ after $T$; objective $x_\infty(x(T), y(T), \sigma_f) + \kappa\int_0^T \sigma$. Every optimal control is mild on $[0, t^*)$, strict on $[t^*, t^* + \eta)$ and mild on $[t^* + \eta, T]$ with $0 \le \eta \le \tau$.

Let $\hat x(t)$ denote the susceptible fraction of the uncontrolled epidemic, that is the solution with $\sigma \equiv \sigma_f$ from $(x_0, y_0)$.

**Theorem (complete quarantine, no running cost).** Let $\sigma_s = 0$, $\sigma_m = \sigma_f > 0$ and $\kappa = 0$. The optimal control is unique and is the single strict interval $[t^*, t^* + \eta)$ given by:

1. if $x_0 \le 1/\sigma_f$: $t^* = 0$ and $\eta = \tau$;
2. if $x_0 > 1/\sigma_f$ and $\hat x(T - \tau) \le 1/\sigma_f$: $\eta = \tau$ and $t^* = \bar t$, the unique time in $[0, T - \tau]$ with $\hat x(\bar t) = 1/\sigma_f$;
3. if $1/\sigma_f < \hat x(T - \tau) \le \dfrac{1}{\sigma_f (1 - e^{-\gamma\tau})}$: $t^* = T - \tau$ and $\eta = \tau$;
4. if $\hat x(T - \tau) > \dfrac{1}{\sigma_f (1 - e^{-\gamma\tau})}$: $\eta = T - \tilde t$, where $\tilde t$ is the unique time in $[T - \tau, T]$ with

    $$
    \hat x(\tilde t) = \frac{1}{\sigma_f\big(1 - e^{-\gamma (T - \tilde t)}\big)} .
    $$

In case 2 the complete quarantine starts exactly at the peak of infections of the uncontrolled epidemic, where $\hat x = 1/\sigma_f$ and $y' = 0$, and uses its whole budget. In case 4 the epidemic is still far from herd immunity late in the window, so the quarantine is started late and runs to $T$; its length $T - \tilde t$ is strictly shorter than the budget $\tau$ when $\tilde t > T - \tau$, so using less than the allowed strict quarantine can be optimal. With $\tau = T$ the regimes collapse to $t^* = 0$ when $x_0 \le 1/(\sigma_f(1 - e^{-\gamma T}))$ and $t^* = \tilde t$ otherwise, which is the single-switch optimal intervention of the finite-window SIR problem without a budget.

**Partial quarantine and cost.** For $0 \le \sigma_s < 1$, $\sigma_m = \sigma_f$ and $\kappa = 0$ the optimal control is again unique with the same four regimes (onset at $0$, at an interior time with full budget, at $T - \tau$, or late with a truncated strict phase), where the interior onset is the unique zero in $(0, T - \tau]$ of a function with the sign of

$$
z(t) = \int_t^{t + \tau} \frac{\sigma_f\, x_{t,\tau}(r) - 1}{y_{t,\tau}(r)}\, dr ,
$$

where $(x_{t,\tau}, y_{t,\tau})$ is the trajectory under strict quarantine on $[t, t + \tau]$; $z$ changes sign at most once, from positive to negative, on $[0, T - \tau]$. For $\kappa > 0$ and $0 \le \sigma_s < \sigma_m \le \sigma_f$ with $\sigma_s < 1$, if $\kappa$ is small enough that lengthening the strict phase always increases $J$, the optimal control is again unique with the analogous four regimes; if $\kappa$ is so large that lengthening always decreases $J$, the optimal control is $\sigma^* \equiv \sigma_m$ with no strict quarantine at all.

## Depends on

- [Bang-bang optimal quarantine with a strict-phase time budget](bang-bang-optimal-quarantine-with-a-strict-phase-time-budget.md)

## Expansion

By the bang-bang structure it suffices to maximize $J(t_1, \eta)$ over $\{0 \le \eta \le \tau,\ 0 \le t_1 \le T - \eta\}$. With $\kappa = 0$ one has $\partial J/\partial\eta > 0$, so the maximum lies on the upper boundary: $\eta = \tau$ for $t_1 \le T - \tau$ and $\eta = T - t_1$ afterwards. Along the first piece $dJ/dt_1$ is a positive multiple of a function $w(t_1)$ with the sign of $z(t_1)$, and $z$ is decreasing on the only interval where its sign is not forced, so $J$ increases and then decreases. Along the second piece the derivative has the sign of $\gamma(\sigma_f - \sigma_s) h(t_1) - 1$ with $h(t) = y_{t}(T)\int_t^T x_{t}(s)/y_{t}(s)\, ds$ decreasing and $h(T) = 0$. When $\sigma_s = 0$ the infected fraction decays as $e^{-\gamma(r - t)}$ during quarantine while $x$ is frozen, so $z(t)$ reduces to a positive multiple of $\sigma_f \hat x(t) - 1$, and the comparison at $t = T - \tau$ becomes the explicit threshold $1/(\sigma_f(1 - e^{-\gamma\tau}))$.

## Sources

- R. Balderrama, J. Peressutti, J. P. Pinasco, F. Vazquez, C. Sánchez de la Vega, "Optimal control for a SIR epidemic model with limited quarantine", Scientific Reports 12 (2022), 12583; Methods section, Eqs. (30) to (54), Remarks 2 and 3, Lemmas 5 and 6, Theorems 2 and 3 and Corollary 1. <https://doi.org/10.1038/s41598-022-16619-z> (PMCID: PMC9307862).
- D. I. Ketcheson, "Optimal control of an SIR epidemic through finite-time non-pharmaceutical intervention", Journal of Mathematical Biology 83 (2021), 7, Theorem 3, recovered as the case $\tau = T$. <https://doi.org/10.1007/s00285-021-01628-9>.
