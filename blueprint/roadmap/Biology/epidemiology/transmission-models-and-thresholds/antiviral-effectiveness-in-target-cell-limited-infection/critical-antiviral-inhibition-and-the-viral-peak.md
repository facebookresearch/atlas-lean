# Critical antiviral inhibition and the viral peak

**Model.** Uninfected target cells $U$, infected cells $I$ and virus $V$ obey

$$\dot U = -\beta(1-\eta_\beta(t))UV, \qquad \dot I = \beta(1-\eta_\beta(t))UV - \delta I, \qquad \dot V = p(1-\eta_p(t))I - cV,$$

on $\mathbb{R}^3_{\ge0}$, with $\beta, \delta, p, c > 0$. Treatment starting at time $t_{tr}$ sets the inhibition of infection $\eta_\beta(t)$ and of replication $\eta_p(t)$ from $0$ to constants $\eta_\beta, \eta_p \in [0,1)$ for $t \ge t_{tr}$. Without treatment, if $U(0) > U_c = c\delta/(\beta p)$, $I(0) = 0$ and $V(0) > 0$, the virus has a local minimum at $\check t_V$ and a peak at $\hat t_V > \check t_V$. A treatment started at $t_{tr} \in (\check t_V, \hat t_V)$ is *effective* if the treated virus peaks at $\hat t_{V,tr} < \hat t_V$, and *ineffective* otherwise. The within-host reproduction number at treatment time and the critical inhibition are

$$\mathcal R(t_{tr}) = \frac{U(t_{tr})\,p(1-\eta_p)\,\beta(1-\eta_\beta)}{c\delta}, \qquad \eta^c(t_{tr}) = 1 - \frac{c\delta}{U(t_{tr})\beta p},$$

the same critical value for $\eta_p$ and $\eta_\beta$; it increases with $U(t_{tr})$, so it decreases as treatment is delayed, approaching $0$ near the untreated peak.

**Theorem.** Let $t_{tr} \in (\check t_V, \hat t_V)$ and consider one inhibition $\eta \in \{\eta_p, \eta_\beta\}$ at a time.
1. If $\eta > \eta^c(t_{tr})$, the virus peaks at $t_{tr}$ itself and decreases afterwards: the treatment is effective.
2. If $\eta^c(t_{tr}) < \eta_1 < \eta_2$, both treatments are effective and the stronger one gives a lower viral load, $V_2(t) < V_1(t)$ on some interval $(t_{tr}, t^*]$.
3. If $\eta < \eta^c(t_{tr})$, the virus peaks at some $\hat t_{V,tr} > t_{tr}$, and there is an early-treatment time $t_e(\eta, t_{tr})$ such that $\hat t_{V,tr} > \hat t_V$ for $t_{tr} \in (\check t_V, t_e]$: the treatment is ineffective.
4. If $\eta_1 < \eta_2 < \eta^c(t_{tr})$ and $t_{tr} \in (\check t_V, t_e]$, then $\hat t_{V,tr,2} > \hat t_{V,tr,1} > \hat t_V$: both are ineffective and the stronger sub-critical treatment delays the peak more.

## Expansion

The proof uses the quasi-steady approximation $I \approx (c/p)V$, under which $\dot V \approx (\mathcal R(t) - 1)\delta V$ with $\mathcal R(t)$ proportional to $U(t)$. Before the untreated peak $\mathcal R(t) > 1$. A super-critical drug makes $\mathcal R$ jump below 1 at $t_{tr}$, and because $U$ only decreases, $\mathcal R$ stays below 1, so $V$ decreases from $t_{tr}$ on. A sub-critical drug leaves $\mathcal R > 1$ but smaller, so the virus keeps growing more slowly; target cells are consumed more slowly, and $U$ reaches the (raised) critical level later, which postpones the peak. A stronger sub-critical drug slows consumption further, hence the counter-intuitive ordering of peak times in part 4.

## Sources

- P. Abuin, A. Anderson, A. Ferramosca, E. A. Hernandez-Vargas, A. H. González, "Dynamical characterization of antiviral effects in COVID-19", Annual Reviews in Control (2021), Eqs. (2.1)–(2.2), (3.1)–(3.3), Definition 4, Theorem 3.1 and Appendix A, <https://doi.org/10.1016/j.arcontrol.2021.05.001>, PMCID PMC8162791.
