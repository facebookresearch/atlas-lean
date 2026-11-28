# Reinfection threshold for backward bifurcation in a recurrent tuberculosis model

**Model.** Susceptible $S$, latently infected $E$, actively infectious $I$ and recovered $R$ individuals, with $N = S + E + I + R$ and frequency-dependent force of infection $\lambda = c\beta I / N$, satisfy

$$\begin{aligned}
\dot S &= \Lambda - \lambda S - \mu S, \\
\dot E &= (1-q)\lambda S + (1-\sigma)\theta\lambda R - p\lambda E - (k+\mu) E, \\
\dot I &= q\lambda S + \sigma\theta\lambda R + p\lambda E + kE - (\mu + r + \mu_d) I, \\
\dot R &= rI - \theta\lambda R - \mu R,
\end{aligned}$$

with recruitment $\Lambda$, natural mortality $\mu$, TB mortality $\mu_d$, treatment/recovery rate $r$, reactivation rate $k$, fraction $q \in [0,1]$ of new infections progressing fast, relative susceptibility $p \ge 0$ of latently infected individuals to exogenous reinfection, relative susceptibility $\theta \ge 0$ of recovered individuals to reinfection, and probability $\sigma \in [0,1]$ of fast progression after reinfection of a recovered individual. All parameters are positive except where stated; $N$ varies in time.

**Reproduction number.** The disease-free equilibrium $(\Lambda/\mu, 0, 0, 0)$ is locally asymptotically stable if

$$\mathcal R_0 = \frac{c\beta\, (k + \mu q)}{(\mu + k)(\mu + r + \mu_d)} < 1$$

and unstable if $\mathcal R_0 > 1$; $\mathcal R_0$ does not involve the reinfection parameters $p, \theta, \sigma$.

**Theorem (recurrent TB alone, $p = 0$).** Endemic equilibria correspond to positive roots $\lambda^*$ of $b_2 \lambda^2 + b_1 \lambda + b_0 = 0$ with $b_2 > 0$ and $b_0 \propto 1 - \mathcal R_0$. At $\mathcal R_0 = 1$ the system undergoes a backward bifurcation if

$$\theta > \theta_c = \frac{(\mu + r)(\mu + k) + \mu \mu_d (1 - q)}{r\,(k + \mu\sigma)},$$

and a forward bifurcation if $\theta < \theta_c$. In the backward case two positive endemic equilibria exist for $\mathcal R_0$ in an interval $(\mathcal R_c, 1)$, where $\mathcal R_c$ is defined by vanishing discriminant $b_1^2 - 4 b_2 b_0 = 0$, and TB can persist when $\mathcal R_0 < 1$.

**Reinfection of latents ($p > 0$).** With all pathways present, equilibria are given by positive roots of a cubic in $\lambda$; there is a critical exogenous-reinfection level $p_c$ (decreasing as recurrent-TB reinfection $\theta$ grows) above which the bifurcation at $\mathcal R_0 = 1$ is backward. Even with a forward bifurcation, the cubic can produce a hysteresis loop of endemic states to the left of $\mathcal R_0 = 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Proof depends on

- [Quadratic endemic-equilibrium condition for backward bifurcation](../backward-bifurcation/quadratic-endemic-equilibrium-condition-for-backward-bifurcation.md)

## Expansion

The fraction $(k + \mu q)/(\mu + k)$ of new infections eventually becomes infectious (fast progression, or latency survived until reactivation), each infectious case lasts $1/(\mu + r + \mu_d)$ and infects at rate $c\beta$; this gives $\mathcal R_0$ by the next-generation method. For the threshold, fix $\lambda$ at equilibrium: $S = \Lambda/(\lambda + \mu)$, $R = rI/(\theta\lambda + \mu)$, eliminate $E$, and use $N = (\Lambda - \mu_d I)/\mu$ to write $I = \lambda\Lambda/(c\beta\mu + \mu_d\lambda)$. Clearing denominators gives a quadratic with leading coefficient $\theta[\mu(\mu + k) + r\mu(1 - \sigma) + \mu\mu_d(1-q)] > 0$ and constant term proportional to $1 - \mathcal R_0$. At $\mathcal R_0 = 1$, substituting $c\beta(k + \mu q) = (\mu + k)(\mu + r + \mu_d)$, the linear coefficient becomes $(\mu + r)(\mu + k) + \mu\mu_d(1 - q) - \theta r (k + \mu\sigma)$, negative exactly when $\theta > \theta_c$; a negative linear coefficient with $b_0 > 0$ small (for $\mathcal R_0$ just below one) gives two positive roots. Recovered individuals are estimated to be several times more susceptible than TB-naive ones, which places $\theta$ in the range where recurrent TB can by itself create bistability.

## Sources

- I. M. Wangari, L. Stone, "Backward bifurcation and hysteresis in models of recurrent tuberculosis", PLoS ONE (2018), model (Eqs. 1–2), basic reproduction number (Eq. 3) and Theorem 1, cubic equilibrium polynomial (Eqs. 4–5), Lemmas 1–3 and threshold $p_c$ (Eqs. 13–15), hysteresis, and the subsystem without reinfection of latents (Eqs. 18–21) with Theorem 2. <https://doi.org/10.1371/journal.pone.0194256> (PMC5863985).
