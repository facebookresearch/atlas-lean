# Dengue persistence threshold under partial Wolbachia invasion

Consider a host–vector SEIR–SEI model for dengue with constant human population $H$ (birth and death rate $b_H$, incubation rate $\gamma_H$, recovery rate $\sigma_H$), coupled to a mosquito population in the high-birth-rate limit, where the total mosquito population equals the carrying capacity $K$ and a fraction $p(t)$ carries *Wolbachia*. Wild mosquitoes ($K(1-p)$ in total) have death rate $d_M$, incubation rate $\gamma_M$ and bite-transmission rates $\beta_{HM}$ (human to mosquito) and $\beta_{MH}$ (mosquito to human). *Wolbachia* carriers ($Kp$ in total) have $d_W$, $\gamma_W$, $\beta_{HW}$, $\beta_{WH}$, with $\beta_{WH} < \beta_{HW}$. Define the per-stage (host-to-vector-to-host) reproduction numbers of the two pure mosquito populations by

$$(R_0^M)^2 = \frac{\beta_{HM}\beta_{MH} K \gamma_M \gamma_H}{H d_M (b_H + \sigma_H)(\gamma_M + d_M)(\gamma_H + b_H)}, \qquad (R_0^W)^2 = \frac{\beta_{HW}\beta_{WH} K \gamma_W \gamma_H}{H d_W (b_H + \sigma_H)(\gamma_W + d_W)(\gamma_H + b_H)},$$

and, for a limiting *Wolbachia* frequency $p^* \in \{0, \theta, 1\}$ (the zeros of the bistable frequency dynamics $p' = f(p)$),

$$R_{p^*}^2 = (R_0^W)^2\, p^* + (R_0^M)^2\, (1 - p^*).$$

**Theorem (uniform persistence threshold).** Restrict to initial conditions whose frequency satisfies $p(t) \to p^*$.

- If $R_{p^*} > 1$, the system is uniformly persistent: there is $\eta > 0$ such that every solution with a positive initial number of exposed or infected hosts or vectors satisfies $\liminf_{t \to \infty} (E_H + I_H + E_M + I_M + E_W + I_W)(t) > \eta$.
- If $R_{p^*} < 1$, then $(E_H + I_H + E_M + I_M + E_W + I_W)(t) \to 0$.

When $R_{p^*} > 1$, the equilibrium equations have an endemic solution attached to $p^*$, whose components are expressed through the positive root of an explicit quadratic. The basic reproduction number of a population with frequency $p^*$ is the convex combination $R_{p^*}^2$ of the two pure-population basic reproduction numbers. Full invasion ($p^* = 1$) removes outbreaks only if $R_0^W < 1$. With the dengue parameters used in the source, $(R_0^M)^2 \approx 2.83$ and $(R_0^W)^2 \approx 1.08$, so outbreaks remain possible but milder after full replacement.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Impulsive limit of short mosquito releases](impulsive-limit-of-short-mosquito-releases.md)

## Expansion

Since $p' = f(p)$ does not involve the epidemiological variables, $p(t) \to p^*$ reduces the dengue subsystem to an asymptotically autonomous system with wild and *Wolbachia* vector pools of sizes $K(1-p^*)$ and $Kp^*$. The next-generation matrix of the two-stage transmission cycle (human to vector to human) has spectral radius equal to the square root of the expected secondary human cases per human case. Summing over the two vector types, weighted by their share of the vector pool, gives $R_{p^*}^2$. Persistence for $R_{p^*} > 1$ is proved with an average-Lyapunov criterion (Fonda's theorem): on a compact positively invariant set, the boundary set $\{E_H + I_H + E_M + I_M + E_W + I_W = 0\}$ is the zero set of a weighted linear function $P$ of the latent and infectious classes, and $R_{p^*} > 1$ lets one choose the weights so that $\frac{d}{dt} P \ge k P$ for some $k > 0$ along any solution staying near the boundary, which is impossible; hence solutions are repelled from the boundary uniformly.

## Sources

- Almeida L, Bellver-Arnau J, Privat Y, Rebelo C. Vector-borne disease outbreak control via instant releases. *Journal of Mathematical Biology* 89(6):63 (2024), Section 2 (equations (4)–(6), definition of $R_{p^*}^2$, endemic equilibria), Theorem 1 with proof in Appendix B, next-generation computation in Appendix A. <https://doi.org/10.1007/s00285-024-02159-9> (PMCID: PMC11557670)
