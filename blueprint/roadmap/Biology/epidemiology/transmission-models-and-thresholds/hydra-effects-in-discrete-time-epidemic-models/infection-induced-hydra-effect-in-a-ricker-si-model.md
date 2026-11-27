# Infection-induced hydra effect in a Ricker SI model

**Model.** Hosts reproduce with Ricker growth $g(x) = r x e^{-bx}$ ($r > 0$ maximal per-capita growth, $b > 0$ density dependence), survive each generation with probability $1 - d$, and susceptibles escape infection with probability $e^{-\beta I}$. Infected hosts have relative fecundity $w \in [0,1]$ (fecundity reduction $\tilde w = 1 - w$) and extra mortality probability $\mu \in [0,1]$. The disease-free and with-disease systems are

$$\bar S_{t+1} = r\bar S_t e^{-b\bar S_t} + (1 - d)\bar S_t,$$

$$S_{t+1} = r(S_t + wI_t)e^{-b(S_t + wI_t)} + (1 - d)S_t e^{-\beta I_t}, \qquad I_{t+1} = (1 - d)S_t\bigl(1 - e^{-\beta I_t}\bigr) + (1 - d)(1 - \mu)I_t,$$

with total population $T = S + I$. The disease-free fixed point is $\bar S^* = \frac1b \ln\frac rd$ (for $r > d$).

**Hydra effects.** At a fixed point $(S^*, I^*)$, a *classical* hydra effect with respect to a fitness-reducing parameter $\alpha \in \{\tilde w, \mu\}$ means $\partial T^*/\partial\alpha > 0$; at a $k$-cycle, the cycle average of $\partial T_i^*/\partial\alpha$ is positive. An *infection-induced* hydra effect means the with-disease system has a fixed point with $S^* + I^* > \bar S^*$.

1. **Endemic equilibrium.** Let $\nu = (1 - d)(1 - \mu)$ and $C = b(1 - \nu)/(\beta(1 - d))$. If $\tilde w = 0$, an endemic fixed point ($I^* > 0$) exists if and only if $d/r < e^{-C}$, and it is then unique; if $\tilde w > 0$ the same holds when $C \ge 3$ (the convexity condition used in the source's proof of Lemma 4, App. B.5). An endemic fixed point satisfies $S^* + wI^* < \bar S^*$: the *effective reproducing* population is always below the disease-free level.
2. **Mortality hydra implies fecundity hydra.** If $\ln\frac rd < \dfrac{wbd}{\beta(1 - d)}$ and there is a classical hydra effect in $\mu$ at the fixed point ($\partial T^*/\partial\mu > 0$), then there is also one in the fecundity reduction ($\partial T^*/\partial\tilde w > 0$).
3. **Sufficient condition for an infection-induced hydra effect.** If the endemic fixed point exists (item 1) and

$$w < 1 - \frac{\beta}{b} \qquad\text{and}\qquad d \ge \frac12,$$

then the endemic fixed point has $S^* + I^* > \bar S^*$, regardless of the disease-induced mortality $\mu$.

Numerically, hydra effects are most widespread when the disease-free population cycles: infection can enlarge the time-averaged population across period-doubling and chaotic regimes even where no fixed-point hydra effect exists.

## Expansion

Item 1 reduces the fixed-point equations to a single equation $\ln(1 - Cz) = g(z)$ in $z = \beta I^*/(bS^*)$; the left side is strictly concave on $(0, 1/C)$ and, when $g$ is strictly convex, the graphs meet at a positive $z$ at most once, and exactly once iff $d/r < e^{-C}$. The inequality $S^* + wI^* < \bar S^*$ reflects that Ricker reproduction depends only on the effective density $S + wI$, while the extra loss of infected hosts must be compensated by more reproduction, which for overcompensatory growth occurs at lower effective density. The total $S^* + I^*$ exceeds $\bar S^*$ when the infected class is large but contributes little to density dependence: low $w$ (infected hosts barely reproduce, so they do not depress others' fecundity) and high natural turnover $d$ (so the growth term dominates) give item 3. Item 2 follows by comparing the implicit derivatives of $T^*$ with respect to $\mu$ and $\tilde w$ through the Jacobian of the fixed-point map, using item 1 and the stated bound to fix signs.

## Sources

- L. F. Strube, S. Elgart, L. M. Childs, "Infection-induced increases to population size during cycles in a discrete-time epidemic model", *Journal of Mathematical Biology* (2024), Sections 2–3 (Eqs. (1)–(7), Theorem 1, Lemmas 2–4, Theorem 5) and Appendix B, <https://doi.org/10.1007/s00285-024-02074-z> (PMC11006791).
