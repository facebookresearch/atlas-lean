# Average detection delay under a geometric prior

Let $P_0$ and $P_1$ be probability measures on a measurable space $\mathcal{X}$, $\mathsf{P}_\nu$ the [change-point law](change-point-law.md) with change at observation $\nu$, and suppose that the change point $\Gamma$ has the geometric prior $\pi_\nu = P(\Gamma = \nu) = \rho(1 - \rho)^{\nu - 1}$, $\nu \ge 1$, with $0 < \rho \le 1$ ($\rho = 1$ puts the change at the first observation, with $0^0 = 1$). The average detection delay of an alarm time $\tau : \mathcal{X}^{\mathbb{N}} \to \{0, 1, \dots\} \cup \{\infty\}$ is

$$\mathrm{ADD}(\tau) = \sum_{\nu \ge 1} \pi_\nu\, \mathsf{E}_\nu\big[(\tau - \nu)^+\big] = \mathsf{E}\big[(\tau - \Gamma)^+\big] \in [0, \infty],$$

with $(\tau - \nu)^+ = \infty$ when $\tau = \infty$ (Veeravalli–Banerjee, equations (7) and (11)).

## Sources

- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §III, equations (7) and (11).
