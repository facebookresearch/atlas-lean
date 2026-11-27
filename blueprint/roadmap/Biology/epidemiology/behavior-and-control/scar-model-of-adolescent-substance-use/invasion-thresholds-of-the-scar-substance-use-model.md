# Invasion thresholds of the SCAR substance-use model

**Model.** A school population is split into susceptible $S$, casual users $C$, addicted (problematic) users $A$ and resistant students $R$, $N = S + C + A + R$. Students enter at rate $\mu N$ (a fraction $\rho$ directly resistant) and leave at rate $\mu$; problematic users drop out at rate $\delta$, a fraction $\phi$ re-entering as susceptible. All social interactions use standard incidence:

$$\dot S = \mu(1-\rho)N - \frac{\beta_{CS}CS + \beta_{AS}AS + \beta_{RS}RS - \beta_{RC}RC}{N} - \mu S + \phi\delta A,$$

$$\dot C = \frac{\beta_{CS}CS + \beta_{AS}AS - \beta_{RC}RC - \beta_{AC}AC + \beta_{RA}AR}{N} - \mu C,$$

$$\dot A = \frac{\beta_{AC}AC - \beta_{RA}AR}{N} - (\mu + \delta)A, \qquad \dot R = \mu\rho N + \frac{\beta_{RS}RS}{N} - \mu R .$$

Solutions stay non-negative with $\dot N = -(1-\phi)\delta A \le 0$. In scaled fractions $(x,y,z,w) = (S,C,A,R)/N$:

**Theorem (substance-free state).** The substance-free subsystem has the unique, globally asymptotically stable resistant fraction

$$w_f = \frac{(\beta_{RS} - \mu) + \sqrt{(\beta_{RS}-\mu)^2 + 4\rho\mu\beta_{RS}}}{2\beta_{RS}} .$$

**Theorem (invasion thresholds).** Define

$$\mathcal{R}_y = \frac{\beta_{CS}(1-w_f)}{\mu + \beta_{RC}w_f}, \qquad \mathcal{R}_z^{(c)} = \frac{\beta_{AC}\,y_c^-}{\mu + \delta + \beta_{RA}w_c^-},$$

where $(y_c^-, w_c^-)$ is the lower casual-use equilibrium of the addiction-free subsystem. $\mathcal{R}_y < 1$, equivalently $w_f > w_{\mathrm{thr}} := (\beta_{CS} - \mu)/(\beta_{CS} + \beta_{RC})$, makes the substance-free equilibrium locally asymptotically stable. When the addiction-free subsystem has two interior equilibria ($w_c^- < w_{\mathrm{thr}} < w_c^+$, real when $\Delta = \mu^2(\beta_{CS} - \beta_{RS})^2 - 4\mu\rho\beta_{RS}\beta_{RC}\beta_{CS} \ge 0$), the system is bistable, and if also $\mathcal{R}_z^{(c)} > 1$ problematic use is uniformly persistent.

**Corollary (elimination).** If $\beta_{AC} < \mu + \delta$ then $z(t) \to 0$; if moreover $w_{\mathrm{thr}} < w_c^-$, then also $y(t) \to 0$ and $w(t) \to w_f$.

## Depends on

- [Solutions of the Kermack-McKendrick SIR model](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Resistance spreads socially ($\beta_{RS}$) and is seeded by entry ($\rho$), so $w_f$ solves the quadratic balance $\beta_{RS}w^2 - (\beta_{RS} - \mu)w - \rho\mu = 0$. Casual use invades a population at $w_f$ if the per-user recruitment of susceptibles exceeds exit by graduation plus conversion by resistant peers, which is $\mathcal{R}_y > 1$. Because resistant students convert casual users back ($\beta_{RC}RC$), the casual-use subsystem can have a backward-bifurcation-like pair of equilibria and hysteresis: lowering peer influence below the invasion threshold need not eliminate established use. The bound $\beta_{AC} < \mu+\delta$ works because $\dot z \le (\beta_{AC}y - \mu - \delta)z$ and $y \le 1$.

## Sources

- T. Pizarro, J. Su, Y. He, Y. Kang, "SCAR dynamics of adolescent substance use: peer influence, dropout, and bifurcation structure in a school-based model", *CSIAM Transactions on Life Sciences* (2026), system (eq:fullmod), Theorems 3.1-3.5 and Corollary 3.7, <https://doi.org/10.4208/csiam-ls.so-2026-0531> (preprint arXiv:2606.12564).
