# Density phase transition for an SIS infection on the zero-range process

**Model.** Particles on $\mathbb{Z}^d$ ($d \ge 1$) move as a zero-range process: a site with $n$ particles emits one particle at rate $g(n)$ to a uniformly chosen nearest neighbour, where $g(0) = 0$ and

$$\Gamma_- \le g(n) - g(n-1) \le \Gamma_+, \qquad n \ge 1,$$

for constants $0 < \Gamma_- \le 1 \le \Gamma_+$. The process starts from its product invariant measure $\mu_\rho$ of density $\rho > 0$. Each particle is healthy or infected; a healthy particle sharing a site with an infected one is infected instantaneously, and an infected particle that is alone (among infected particles) at its site recovers at rate $\delta \in (0, \infty]$. Initially only the particles at the origin are infected. The infection *survives* if at all times some particle is infected.

**Theorem.**
1. For every $\delta > 0$ there is $\bar\rho(\delta) > 0$ such that the infection dies out almost surely for all $\rho \in (0, \bar\rho]$.
2. There is $\rho_\star < \infty$ such that for every $\rho \ge \rho_\star$ the infection survives with positive probability for every $\delta \in [0, \infty]$, including instantaneous healing.
3. Consequently, for each $\delta \in (0, \infty]$ there is a critical density $\rho_c(\delta) \in (0, \infty)$: extinction a.s. for $\rho < \rho_c(\delta)$, survival with positive probability for $\rho > \rho_c(\delta)$.
4. For every $\rho > 0$ there is $\delta_\star(\rho) > 0$ with survival for all $\delta \le \delta_\star(\rho)$, and for $\rho < \rho_c(\infty-)$ there is a critical healing rate $\delta_c(\rho) \in (0, \infty)$ separating survival ($\delta < \delta_c$) from extinction ($\delta > \delta_c$).

## Expansion

This extends the Kesten–Sidoravicius model of infection spreading among independent random walkers to interacting (zero-range) motion. Monotonicity of survival in $\rho$ and $\delta$ turns the extinction and survival regimes into sharp thresholds. Both directions are proved by multiscale renormalization over space-time boxes, which needs decoupling inequalities for the zero-range environment: horizontal decoupling for separated boxes and vertical decoupling with sprinkling (a small density increase) for time-separated boxes. At low density infected clusters are too sparse to meet before healing; at high density the environment is dense enough that infected particles keep meeting healthy ones even under instantaneous healing.

## Sources

- R. Baldasso, M. R. Hilario and I. Ornelas, "Epidemic Phase Transitions in the Zero-Range Process", arXiv:2607.22908 (2026), Theorems 1.1–1.7, <https://doi.org/10.48550/arXiv.2607.22908>.
