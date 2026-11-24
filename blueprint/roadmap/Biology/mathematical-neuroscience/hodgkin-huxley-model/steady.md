# Steady state α/(α + β) of the gating kinetics

For functions $\alpha, \beta \colon \mathbb{R} \to \mathbb{R}$ and a voltage $V$, the steady state
of the [gating kinetics](gate.md) is

$$y_\infty(V) = \frac{\alpha(V)}{\alpha(V) + \beta(V)},$$

with the convention $x/0 = 0$: it is $0$ when $\alpha(V) + \beta(V) = 0$. For $\alpha(V) > 0$ and
$\beta(V) > 0$ the denominator is positive, $y_\infty(V)$ [lies in $(0, 1)$](steady-mem-ioo.md), and
it is the [only zero of the gating kinetics](gate-eq-zero-iff.md) at $V$.
