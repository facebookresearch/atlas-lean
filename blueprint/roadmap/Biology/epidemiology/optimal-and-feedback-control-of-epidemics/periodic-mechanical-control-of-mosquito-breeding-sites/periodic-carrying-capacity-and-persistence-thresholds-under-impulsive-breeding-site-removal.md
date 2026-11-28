# Periodic carrying capacity and persistence thresholds under impulsive breeding-site removal

**Model.** Aquatic stages $L_v$ and adult females $A_v$ satisfy

$$\frac{dL_v}{dt} = rbA_v\Big(1 - \frac{L_v}{K_v}\Big) - (\nu_L + \mu_L)L_v, \qquad \frac{dA_v}{dt} = \nu_L L_v - \mu_v A_v,$$

with sex ratio $r$, daily egg output $b$, maturation rate $\nu_L$ and mortalities $\mu_L, \mu_v > 0$. The **basic offspring number** is

$$\mathcal N = \frac{\nu_L\, r b}{(\nu_L + \mu_L)\,\mu_v}.$$

For constant $K_v > 0$ the compact set $\mathcal K = \{(L_v, A_v) \in \mathbb R^2_+ : L_v \le K_v,\ A_v \le \tfrac{\nu_L}{\mu_v}K_v\}$ is positively invariant, and for initial data in $\mathcal K$: if $\mathcal N \le 1$ the trivial equilibrium is globally asymptotically stable, and if $\mathcal N > 1$ the positive equilibrium is globally asymptotically stable.

**Impulsive control.** Breeding sites regrow linearly toward $K_{\max}$ at rate $r_K$ and a public agent removes a fraction $\gamma(H) \in (0,1)$ of them every $\tau$ days, the fraction depending on the level $H$ of household protective behavior:

$$\frac{dK_v}{dt} = r_K(K_{\max} - K_v), \qquad K_v\big((n\tau)^+\big) = \big(1 - \gamma(H(n\tau))\big)K_v(n\tau).$$

**Proposition (periodic carrying capacity).** If $H \equiv H_0$, the impulsive equation has the $\tau$-periodic solution

$$K_{v,per}(t) = \Big(1 - \frac{\gamma(H_0)\,e^{-r_K(t - n\tau)}}{1 - (1 - \gamma(H_0))e^{-r_K\tau}}\Big)K_{\max}, \qquad t \in [n\tau,(n+1)\tau),$$

and every solution converges to it.

**Proposition (persistence and extinction thresholds).** Let $H(t) \to H_0$ and $C = r_K\,\gamma(H_0)/(1 - e^{-r_K\tau})$, and take initial data of the mosquito subsystem in $\mathcal K$ with $K_{\max}$ (which bounds $K_v$) in place of $K_v$.

- If $\displaystyle \mathcal N > \Big(1 + \frac{\mu_v}{\nu_L}\frac{C}{1-\gamma(H_0)}\Big)\Big(1 + \frac{1}{\nu_L + \mu_L}\frac{C}{1-\gamma(H_0)}\Big)$, the coupled system has a unique positive $\tau$-periodic solution that attracts all nontrivial initial data in this set.
- If $\displaystyle \mathcal N \le \Big(1 + \frac{\mu_v}{\nu_L}C\Big)\Big(1 + \frac{1}{\nu_L + \mu_L}C\Big)$, every solution with initial data in this set converges to the trivial equilibrium: the mosquito population is eliminated.

Since $C$ increases with $\gamma(H_0)$, households that reduce their own protective effort in response to public mechanical control lower $\gamma(H_0)$, which shrinks both thresholds and can switch the outcome from elimination to persistence.

## Expansion

The carrying-capacity equation is linear between pulses, so the stroboscopic map $K \mapsto (1-\gamma)\big(K_{\max} + (K - K_{\max})e^{-r_K\tau}\big)$ is a contraction with the explicit fixed point that generates $K_{v,per}$. The mosquito subsystem with $K_v = K_{v,per}(t)$ is a $\tau$-periodic cooperative system that is concave in the sense of decreasing Jacobians, so a periodic threshold theorem for such systems (attractivity of zero or of a unique positive periodic orbit, decided by the sign pattern of the time-averaged linearization) applies. The explicit bounds $\frac{(1-\gamma)(1-e^{-r_K\tau})}{1-(1-\gamma)e^{-r_K\tau}}K_{\max} \le K_{v,per} \le \frac{1-e^{-r_K\tau}}{1-(1-\gamma)e^{-r_K\tau}}K_{\max}$ on the periodic carrying capacity enter the comparison, which is why the sufficient conditions for persistence and for extinction differ by the factor $1/(1-\gamma(H_0))$.

## Sources

- Y. Dumont, J. Thuilliez, "Human behaviors: A threat to mosquito control?", Mathematical Biosciences 281 (2016), 9–23, <https://doi.org/10.1016/j.mbs.2016.08.011>. Published version of arXiv:1510.06796, cited next; locators there refer to the arXiv version.
- Y. Dumont, J. Thuilliez, "Human behaviors: a threat for mosquito control?", arXiv (2015). Propositions 1–5, Theorem 1 (periodic cooperative systems). <https://doi.org/10.48550/arXiv.1510.06796>
