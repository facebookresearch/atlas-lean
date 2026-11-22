# Shiryaev's alarm time

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. Suppose that the change point has the geometric prior $\rho(1 - \rho)^{\nu-1}$, $\nu \ge 1$, with $0 < \rho \le 1$, and let $p_n$ be [Shiryaev's posterior statistic](shiryaev-posterior.md). For a threshold $A \in \mathbb{R}$, Shiryaev's alarm time is

$$\tau_S = \inf\{n \ge 1 : p_n \ge A\},$$

with $\tau_S = \infty$ if no alarm is raised (Veeravalli–Banerjee, equation (15)).

## Sources

- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §III-A, equation (15).
