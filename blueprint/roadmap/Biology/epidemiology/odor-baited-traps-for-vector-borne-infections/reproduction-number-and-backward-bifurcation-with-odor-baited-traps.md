# Reproduction number and backward bifurcation with odor-baited traps

**Model.** Hosts $(S_H, I_H, R_H)$ and mosquitoes $(S_M, I_M)$ interact while $L$ odor-baited traps compete with hosts for mosquito visits; $A$ denotes the total attractiveness of hosts and traps (host attractiveness $\alpha$ each), $b\rho$ the trap capture-and-kill rate:

$$S_H' = \Lambda_H - dS_H - \beta_H\alpha\frac{I_M}{A}S_H + \delta R_H, \qquad I_H' = \beta_H\alpha\frac{I_M}{A}S_H - (d + \gamma + \xi)I_H, \qquad R_H' = \gamma I_H - (\delta + d)R_H,$$
$$S_M' = \Lambda_M - \mu S_M - \beta_M\frac{I_H}{A}S_M - b\rho S_M\frac{L}{A}, \qquad I_M' = \beta_M\frac{I_H}{A}S_M - \mu I_M - b\rho I_M\frac{L}{A},$$

with recovery $\gamma$, disease mortality $\xi$, waning immunity $\delta$, and trap-free equilibria $\bar N_H = \Lambda_H/d$, $\bar N_M = \Lambda_M/\mu$. The region $\{S_H + I_H + R_H \le \bar N_H,\ S_M + I_M \le \bar N_M\}$ is positively invariant and attracting.

**Reproduction number.** By the next-generation method,

$$\mathcal{R}_0 = \sqrt{\frac{\beta_H\beta_M\,\bar N_H\bar N_M\,\alpha\mu}{(\gamma + d + \xi)\bigl[(\mu + b\rho)L + \alpha\mu\bar N_H\bigr]^2}} = \sqrt{\frac{\beta_H\beta_M\frac{\bar N_M}{\bar N_H}\alpha}{(\gamma + d + \xi)\,\mu\bigl[(1 + \frac{b\rho}{\mu})\frac{L}{\bar N_H} + \alpha\bigr]^2}},$$

and the disease-free equilibrium is locally asymptotically stable when $\mathcal{R}_0 < 1$.

**Theorem (endemic equilibria).** The system has a unique positive equilibrium if $\mathcal{R}_0 > 1$ (or under a further coefficient condition), two positive equilibria when the quadratic's coefficients satisfy the source's two-root condition, and none otherwise; the source gives a criterion for a backward bifurcation at $\mathcal{R}_0 = 1$, in which case reducing $\mathcal{R}_0$ just below one does not eliminate infection.

## Expansion

Traps act twice: they dilute bites by inflating the denominator $A$ (mosquitoes waste visits on traps), and they kill mosquitoes that visit them, raising effective vector mortality from $\mu$ to $\mu + b\rho L/A$. Both effects appear in the squared bracket of $\mathcal{R}_0$, so $\mathcal{R}_0$ decreases roughly like $1/L$ for many traps. The square root reflects the two-step host-vector-host cycle. Endemic equilibria solve a quadratic whose coefficients are expressed through $\mathcal{R}_0$; when its linear coefficient is negative while $\mathcal{R}_0 < 1$, two positive roots exist, which is the backward bifurcation.

## Sources

- H. Zhong, M. Lima, A. Pugliese, M. Sabbatino, "On the effectiveness of odor-baited traps on mosquito-borne infections" (2025), system (endemic), Proposition 1, the $\mathcal{R}_0$ formula of Section 2, Theorems 1-2, <https://doi.org/10.48550/arXiv.2509.23397>.
