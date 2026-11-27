# Monostable and bistable fronts of virus spread with a bell-shaped immune response

**Model.** The normalized viral concentration $v(x,t) \ge 0$ on $x \in \mathbb R$ obeys (after rescaling to unit diffusion and replication rate)

$$\frac{\partial v}{\partial t} = \frac{\partial^2 v}{\partial x^2} + F(v), \qquad F(v) = v\bigl(1 - v - f(v)\bigr),$$

where $f \ge 0$ is a $C^2$ immune-elimination function (cytotoxic T-cell response) that rises and then falls with viral load. Suppose $F$ has zeros $0 < v_1 < v_2 < v_3$ with $F > 0$ on $(0, v_1)$, $F < 0$ on $(v_1, v_2)$ and $F > 0$ on $(v_2, v_3)$, so $v = 0$ and $v = v_2$ are unstable and $v_1$ (low-level infection) and $v_3$ (high-level infection) are stable. Travelling waves $v = w(x - ct)$ solve

$$w'' + c\, w' + F(w) = 0 .$$

**Low-level (monostable) waves.** Fronts with $w(-\infty) = v_1$, $w(+\infty) = 0$ exist for every $c \ge c_0$. If $f' \ge 0$ on $[0, v_1]$, then $F'(w) \le F'(0)$ there, and the minimal speed is the linear (pulled) speed

$$c_0 = 2\sqrt{F'(0)} = 2\sqrt{1 - f(0)} .$$

**High-level (bistable) waves.** Fronts with $w(-\infty) = v_3$, $w(+\infty) = v_1$ exist for a unique speed $c = c_1$, and

$$c_1 = \frac{\int_{v_1}^{v_3} F(w)\, dw}{\int_{-\infty}^{\infty} w'(x)^2\, dx},$$

so $c_1 > 0$ (high-level infection invades) if and only if $\int_{v_1}^{v_3} F(w)\, dw > 0$, that is

$$\int_{v_1}^{v_3} v f(v)\, dv < \tfrac12 (v_3^2 - v_1^2) - \tfrac13 (v_3^3 - v_1^3).$$

**Regimes.** Two-step waves connecting $v_3$ to $0$ exist only if $c_0 < c_1$. For the step initial datum $v(x, 0) = v^*$ on $x < 0$ and $v(x, 0) = 0$ on $x \ge 0$: if $v^* < v_2$, infection spreads at speed $c_0$ to the level $v_1$; if $v^* > v_2$, $\int_{v_1}^{v_3} F > 0$ and $c_1 \le c_0$, a low-level front moving at $c_0$ is followed by a slower front at $c_1$ raising the load to $v_3$; if $v^* > v_2$ and $c_1 > c_0$, a single high-level front spreads. (For a localized initial bump the bistable part has a width-dependent nucleation threshold, so $v^* > v_2$ alone does not give the high-level front.)

## Depends on

- [Fronts of speed c exist exactly for c at or above the minimal speed](../fisher-kpp-travelling-waves/exists-is-front-iff.md)

## Expansion

Multiplying the travelling-wave equation by $w'$ and integrating over $\mathbb R$ gives $c \int (w')^2 = -\int F(w) w'\, dx = \int_{v_1}^{v_3} F(w)\, dw$ (the boundary terms of $(w')^2/2$ vanish), so the sign of the bistable speed is the sign of the area under $F$ between the two stable states. Near $0$ the problem is of Fisher–KPP type: linearizing gives $w'' + c w' + F'(0) w = 0$, whose roots are real (needed for a positive monotone front) iff $c^2 \ge 4F'(0)$; when $F$ lies below its tangent at $0$ the minimal speed equals this linear bound. With an explicit delay $\tau$ in the immune response, the reaction term becomes $v(1 - v - f(v(x, t-\tau)))$; for a piecewise-constant bistable $f$ there is a unique positive speed for each $\tau$ under a positivity condition, and the speed decreases as the delay grows, so slower immune recruitment slows the spread.

## Sources

- G. Bocharov, A. Meyerhans, N. Bessonov, S. Trofimchuk, V. Volpert, "Spatiotemporal Dynamics of Virus Infection Spreading in Tissues", PLoS ONE (2016), "Virus spread without time delay" (Eqs. 3–5), "Existence of waves" (Eqs. 8–9), "Determination of wave speeds" (Eqs. 13–15), regimes of infection spreading, and the delayed model with Propositions 1–2 (Eqs. 29, 34). <https://doi.org/10.1371/journal.pone.0168576> (PMC5173377).
