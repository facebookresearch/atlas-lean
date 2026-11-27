# Optimal individual vaccination timing in the SIR model

**Setting.** An epidemic without vital dynamics follows the SIR model with vaccination, written with measures to allow instantaneous vaccination:

$$
\begin{cases}
dS(t) = -\beta S(t) I(t)\,dt - dU(t), & S(0^-) = S_{0^-},\\
dI(t) = \big(\beta S(t) I(t) - \gamma I(t)\big)\,dt, & I(0^-) = I_{0^-},
\end{cases}
$$

with $\beta, \gamma > 0$, $(S, I)$ in the closure of $\Omega = \{(S,I) : S, I > 0,\ S + I < 1\}$, and $U$ a nondecreasing societal vaccination policy. A single susceptible individual cannot influence $U$. Its cumulative probability of infection by time $t$ is

$$
\varphi_I(t) = 1 - \exp\Big(-\int_{0^-}^{t} \beta I(\tau)\,d\tau\Big).
$$

Infection costs $r_I > 0$ and vaccination (lifelong immunity, including perceived side effects) costs $r_V > 0$. A mixed strategy is the CDF $\varphi_V$ of the vaccination time ($\varphi_V(0^-) = 0$, $\varphi_V(\infty) \le 1$; mass $1 - \varphi_V(\infty)$ means never vaccinating). Its expected cost is

$$
J(\varphi_V) = r_I\,\varphi_I(\infty) + \int_{0^-}^{\infty} \Big[r_V - r_I\varphi_I(\infty) + (r_I - r_V)\varphi_I(t)\Big]\,d\varphi_V(t).
$$

**Theorem (unbounded vaccination rate).** The minimizer $\varphi_V^*$ of $J$ is:

1. $\varphi_V^* \equiv 0$ (never vaccinate) if $r_I\,\varphi_I(\infty) < r_V$;
2. $d\varphi_V^* = \delta_0$ (vaccinate immediately) if $r_I\,\varphi_I(\infty) > r_V$;
3. $d\varphi_V^* = \alpha\,\delta_0$ with any $\alpha \in [0,1]$ if $r_I\,\varphi_I(\infty) = r_V$.

**Theorem (bounded vaccination rate).** Suppose vaccination capacity is bounded by $u_{\max} < \infty$, so that admissible $\varphi_V$ are nondecreasing, differentiable where $S(t) > 0$, and satisfy $\varphi_V'(t) \le f_V(t)\,(1 - \varphi_V(t))$ with $f_V(t) = u_{\max}/S(t)$. Let $Z_S = \inf\{\tau \ge 0 : S(\tau) = 0\}$. Then:

1. if $r_I \le r_V$, or if $r_I > r_V$ and $\varphi_I(\infty) \le r_V / r_I$, the optimal strategy is $\varphi_V^* \equiv 0$;
2. if $r_I > r_V$ and $\varphi_I(\infty) > r_V/r_I$, the optimal strategy vaccinates at the maximal rate, $\varphi_V^{*\prime}(t) = f_V(t)(1 - \varphi_V^*(t))$ on $[0, \min\{Z_S, \theta_I\})$, and stops afterwards, where $\theta_I$ is the unique solution of

$$
\frac{\varphi_I(\infty) - \varphi_I(\theta_I)}{1 - \varphi_I(\theta_I)} = \frac{r_V}{r_I}.
$$

The left side is the conditional probability of still being infected after $\theta_I$ given escape until $\theta_I$; the individual vaccinates exactly while this residual risk exceeds the cost ratio.

## Depends on

- [Final-size equation of the SIR model](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

Since $J$ is linear in the measure $d\varphi_V$, the optimal strategy places mass only where the integrand $g(t) = r_V - r_I\varphi_I(\infty) + (r_I - r_V)\varphi_I(t)$ is negative. Because $\varphi_I$ is nondecreasing, $g$ is nondecreasing when $r_I > r_V$, so the set where vaccination pays is an initial interval $[0, \theta_I)$; its endpoint is where the residual infection risk equals $r_V/r_I$. Without a capacity constraint all mass moves to $t = 0$; with the constraint, the individual vaccinates as fast as allowed on that interval. If $r_I \le r_V$ vaccination is never cheaper than the worst case of infection.

## Sources

- Laetitia Laguzet, Gabriel Turinici, "Individual Vaccination as Nash Equilibrium in a SIR Model with Application to the 2009–2010 Influenza A (H1N1) Epidemic in France", Bulletin of Mathematical Biology 77 (2015), 1955–1984, <https://doi.org/10.1007/s11538-015-0111-7>. Published version of arXiv:2410.03567, cited next; locators there refer to the arXiv version.
- Laetitia Laguzet, Gabriel Turinici, *Individual vaccination as Nash equilibrium in a SIR model with application to the 2009-10 Influenza A(H1N1) epidemic in France*, arXiv 2024. Appendix C, Theorem 1 (case $u_{\max} < \infty$) and Theorem 2 (case $u_{\max} = \infty$); model in Section 1.1. <https://doi.org/10.48550/arXiv.2410.03567>
