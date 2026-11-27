# Bistability of risk-seeking and risk-averse endemic equilibria in the opinion-driven SIS model

**Model (NOD-SIS).** Let $p(t) \in [0,1]$ be the infected fraction of a well-mixed population and $x(t) \in [-1,1]$ its opinion on contact behaviour ($x < 0$: reduce contacts, risk aversion; $x > 0$: increase contacts, risk seeking; $x = 0$: baseline). With transmissibility $\bar\beta > 0$, recovery rate $\delta > 0$, opinion timescale $\tau_x > 0$, basal urgency $u_0 \ge 0$, infection feedback gain $k_p \ge 0$ and peer-pressure gain $k_x \ge 0$,

$$
\dot p = \bar\beta(1+x)(1-p)p - \delta p, \qquad
\tau_x \dot x = -x + \tanh\bigl((k_p p + k_x x^2 + u_0)\,x\bigr).
$$

The square $\Omega = [0,1]\times[-1,1]$ is positively invariant. Assume $u_0 < 1$ and $k_p + u_0 > 1$ (low basal urgency, but full infection pushes the population to form an opinion), and set $\bar\beta^* = \delta k_p/(k_p - 1 + u_0)$.

**Statement.**

1. *Threshold.* $(0,0)$ (indifferent infection-free) and $(1 - \delta/\bar\beta, 0)$ (indifferent endemic) are equilibria. The infection-free one is locally exponentially stable for $\bar\beta < \delta$ and unstable for $\bar\beta > \delta$; the indifferent endemic one is locally exponentially stable for $\delta < \bar\beta < \bar\beta^*$ and unstable for $\bar\beta > \bar\beta^*$. At $\bar\beta = \delta$ they exchange stability in a transcritical bifurcation, as in the standard SIS model.
2. *SIS equivalence.* For weak peer pressure $k_x < 1/3$ and sufficiently small $u_0$, these are the only equilibria, so steady states coincide with those of the SIS model.
3. *Opinionated equilibria.* Opinionated endemic equilibria $(p^*,x^*)$, $x^* \ne 0$, are the roots of

$$
f_2(x) = \frac{1}{k_p}\Bigl(\frac{\operatorname{arctanh}(x)}{x} - k_x x^2 - u_0\Bigr) + \frac{\delta}{\bar\beta(1+x)} - 1, \qquad p^* = 1 - \frac{\delta}{\bar\beta(1+x^*)}.
$$

If $f_2$ has exactly two roots $x^*_- \le x^*_+$ and $\bar\beta^* < 1$, a second transcritical bifurcation occurs at $\bar\beta = \bar\beta^*$, where the indifferent endemic equilibrium passes its stability to the risk-averse equilibrium $\mathrm{OEE}^- = (p^*_-, x^*_-)$.
4. *Bistability.* Under the same conditions and $\bar\beta > \bar\beta^*$, there are exactly four equilibria; the sign of the opinion is preserved, and every trajectory starting in the interior of $\{x > 0\}$ converges to the risk-seeking equilibrium $\mathrm{OEE}^+$. Moreover

$$
p^*_- \le 1 - \frac{\delta}{\bar\beta} \le p^*_+ ,
$$

so risk seeking raises and risk aversion lowers endemic prevalence relative to the SIS endemic level.

## Depends on

- [Threshold theorem for the SIS model](../../sis-epidemic-model/deriv-infected-pos-iff.md)

## Expansion

Linearizing at $(0,0)$ gives eigenvalues $\bar\beta - \delta$ and $(u_0 - 1)/\tau_x$, and at the indifferent endemic point $\delta - \bar\beta$ and $\bigl(u_0 - 1 + k_p(1 - \delta/\bar\beta)\bigr)/\tau_x$, which changes sign at $\bar\beta^*$. Lyapunov–Schmidt reduction onto the null direction gives nondegenerate transcritical normal forms at both points. Non-indifferent equilibria lie on the opinion nullcline $p = f_1(x) = \frac{1}{k_p}\bigl(\operatorname{arctanh}(x)/x - k_x x^2 - u_0\bigr)$, which is convex and positive for $k_x < 1/3$, intersected with the infection nullcline $p = 1 - \delta/(\bar\beta(1+x))$; small $u_0$ lifts $f_1$ above it. The line $x = 0$ is invariant, so the half-squares $x > 0$ and $x < 0$ are forward invariant. On $x \ge 0$ the off-diagonal Jacobian entries $\bar\beta(1-p)p$ and $\frac{k_p}{\tau_x}x\,\mathrm{sech}^2(\cdot)$ are nonnegative, so the flow is cooperative there and bounded trajectories converge to equilibria. The prevalence ordering follows from $p^* = 1 - \delta/(\bar\beta(1+x^*))$ being increasing in $x^*$.

## Sources

- Marcela Ordorica Arango, Anastasia Bizyaeva, Simon A. Levin and Naomi Ehrich Leonard, "Opinion-driven risk perception and reaction in SIS epidemics", 2025 American Control Conference (ACC) (2025), 4998–5003, <https://doi.org/10.23919/acc63710.2025.11107837>; numbering as in arXiv:2410.12993: Theorem 3.1, Theorems 4.1–4.3 and Corollary 4.1.
