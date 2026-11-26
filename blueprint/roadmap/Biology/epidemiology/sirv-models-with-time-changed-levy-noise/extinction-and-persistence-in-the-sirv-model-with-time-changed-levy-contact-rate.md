# Extinction and persistence in the SIRV model with time-changed Lévy contact rate

**Model.** Susceptible, infected, recovered and vaccinated compartments with total $N = S + I + R + V \le K$ evolve as
$$\begin{aligned}
dS &= \Big(\lambda H - (\rho + \kappa)S - \frac{\tilde\beta(t)I}{N}S + \alpha V + \gamma R\Big)dt, &
dI &= \Big(\frac{\tilde\beta(t)I}{N}S + \delta\frac{\tilde\beta(t)I}{N}V - (\kappa_1 + \theta)I\Big)dt,\\
dR &= \big(\theta I - (\kappa + \gamma)R\big)dt, &
dV &= \Big(\rho S - (\kappa + \alpha)V - \delta\frac{\tilde\beta(t)I}{N}V\Big)dt,
\end{aligned}$$
with recruitment $\lambda H$, vaccination rate $\rho$, waning of vaccine-induced ($\alpha$) and natural ($\gamma$) immunity, natural death $\kappa$, death of infected $\kappa_1 \ge \kappa$, recovery $\theta$ and relative susceptibility $\delta \in [0,1]$ of vaccinated hosts. The contact rate is $\tilde\beta(t) = \tilde\beta_{\max}f(\beta(t))$ with $f \in C^2$, $0 < f_{\min} \le f \le 1$, $|f'| \le K_{f'}$, $|f''| \le K_{f''}$ (and a constant $K_{xf'}$ from assumption (f4)), where $\beta$ solves an SDE driven by a signed random measure $\mu$ that combines a time-changed Brownian part $B$ and a time-changed compensated jump part $\tilde H$, with jump coefficient $\sigma_t(z, \beta)$ and random time-change intensities $\lambda^B_t, \lambda^H_t$.

**Time-change representation.** If $W$ is a Brownian motion and $N$ a centred pure-jump Lévy process with Lévy measure $\nu$, both independent of the time changes, then $B$ is conditionally Gaussian with variance given by the time change $\Lambda^B$ exactly when $B_t \overset{d}{=} W_{\Lambda^B_t}$, and analogously the jump part has the law of $N_{\Lambda^H_t}$.

**Theorem.** For initial values in $(0,\infty)^4$ with $0 < N(0) \le K$ there is a unique global solution, which stays in a positively invariant set $\Gamma$. Let
$$\ell_B = \limsup_{t\to\infty}\frac1t\int_0^t\sigma_s^2(0,\beta(s-))\lambda^B_s\,ds, \qquad \ell_H = \limsup_{t\to\infty}\frac1t\int_0^t\int_{\mathbb R_0}\sigma_s^2(z,\beta(s-))\lambda^H_s\,\nu(dz)\,ds.$$
1. *Extinction.* If
$$\ell_B + \ell_H < \frac{2\big(\kappa_1 + \theta - \tilde\beta_{\max} - K_{xf'}\big)}{K_{f'}^2 + K_{f''}},$$
then $I(t) \to 0$, $R(t) \to 0$ and $\limsup_t (S(t) + V(t)) \le K$ almost surely.
2. *Persistence in mean.* If $\delta > 0$ and
$$\ell_B + \ell_H < \frac{2(1 + f_{\min})\big((1 + f_{\min})(\delta\tilde\beta_{\max}f_{\min} - \kappa_1 - \theta) - K_{xf'}\big)}{K_{f'}^2 + K_{f''}(1 + f_{\min})},$$
then $\liminf_{t\to\infty}\frac1t\int_0^t I(s)\,ds > 0$ almost surely.

## Expansion

Both proofs apply the Itô formula for semimartingales to $\log I(t)$ jointly with $f(\beta(t))$. Writing $\tilde\beta$ through $f(\beta)$, its drift involves $f'$, $f''$ and the time-change intensities, so $\frac1t\log I(t)$ splits into a deterministic rate bounded by the epidemiological parameters, time averages of $\sigma^2\lambda^B$ and $\sigma^2\lambda^H$ weighted by the bounds $K_{f'}^2$ and $K_{f''}$, and local-martingale terms. A strong law of large numbers for local martingales removes the martingale terms. Extinction follows when the resulting upper bound on $\limsup\frac1t\log I$ is negative; persistence follows from a lower bound on $\frac1t\log I$ combined with $\tilde\beta \ge \tilde\beta_{\max}f_{\min}$ and $\delta > 0$, which gives a positive lower bound on the time average of $I$. Larger long-run noise intensities $\ell_B + \ell_H$ shrink both regions.

## Sources

- Giulia Di Nunno, Jasmina Djordjevic and Nenad Suvak, "Epidemic random model under vaccination regime and non-permanent immunity driven by time-changed Levy noise", arXiv:2611.28254 (2026), random SIRV model, assumptions (f1)–(f4), time-change theorem, global positive solution theorem, extinction and persistence theorems, <https://doi.org/10.48550/arXiv.2611.28254>.
