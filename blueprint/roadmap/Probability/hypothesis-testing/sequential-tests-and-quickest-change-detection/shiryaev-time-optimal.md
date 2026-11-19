# Shiryaev's theorem: Bayesian optimality of the Shiryaev rule

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. Assume $P_0 \ne P_1$ and $D(P_1 \,\|\, P_0) < \infty$, let the change point have the geometric prior $\rho(1 - \rho)^{\nu-1}$ with $0 < \rho < 1$, and let $0 < A < 1$ be a threshold whose [Shiryaev rule](shiryaev-time.md) $\tau_S = \inf\{n \ge 1 : p_n \ge A\}$ has [false-alarm probability](false-alarm-prob.md) exactly $\alpha$. Then for every stopping time $\tau$ of the [observation filtration](observation-filtration.md) with $\mathrm{PFA}(\tau) \le \alpha$,

$$\mathrm{ADD}(\tau_S) \le \mathrm{ADD}(\tau),$$

where $\mathrm{ADD}(\tau) = \mathsf{E}[(\tau - \Gamma)^+]$ is the [average detection delay](average-detection-delay.md) (Veeravalli–Banerjee, Theorem 3.1, crediting Shiryaev 1963 and 1978; the hypotheses $P_0 \ne P_1$ and $D(P_1 \| P_0) < \infty$ are that survey's standing assumption $0 < D(f_1 \| f_0) < \infty$).

Veeravalli and Banerjee prove it through a Lagrangian relaxation $\min_\tau \mathsf E(\tau - \Gamma)^+ + \lambda\, P(\tau < \Gamma)$ solved by dynamic programming on the posterior $p_n$.

## Sources

- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §III-A, equations (7)–(16) and Theorem 3.1, crediting A. N. Shiryaev, *On optimum methods in quickest detection problems*, Theory Probab. Appl. 8 (1963) 22–46, and *Optimal Stopping Rules*, Springer, 1978 (originals not consulted; statement as given in that survey).

## Background

- [Optimal stopping and the Snell envelope](../../martingales/optimal-stopping-and-the-snell-envelope/README.md): the relaxed problem is an optimal stopping problem for the posterior process.
- [Optimality of the dynamic programming algorithm](../../../ComputerScience/heuristic-search-and-planning/optimality-of-stationary-policies/is-greatest-n-stage-value.md): dynamic programming for Markov decision processes, the method of the cited proof.
