# Shiryaev's posterior probability of a change

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. Suppose that the change point $\Gamma$ has the geometric prior $\pi_\nu = P(\Gamma = \nu) = \rho(1 - \rho)^{\nu - 1}$, $\nu \ge 1$, with $0 < \rho \le 1$ ($\rho = 1$ puts the change at the first observation, with $0^0 = 1$). Shiryaev's statistic is defined by $p_0 = 0$ and

$$p_{n+1} = \frac{\tilde p_n L(X_{n+1})}{\tilde p_n L(X_{n+1}) + 1 - \tilde p_n}, \qquad \tilde p_n = p_n + (1 - p_n)\rho,$$

with the value $0$ when the denominator vanishes (Veeravalli–Banerjee, equations (12)–(14)). Under the [change-point model](change-point-law.md) with this prior, $p_n$ is the posterior probability that the change has occurred by time $n$, $P(\Gamma \le n \mid X_1, \dots, X_n)$.

## Sources

- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §III-A, equations (12)–(14).
