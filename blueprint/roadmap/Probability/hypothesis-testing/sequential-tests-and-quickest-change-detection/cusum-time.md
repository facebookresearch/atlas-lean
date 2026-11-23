# CUSUM alarm time

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. For a threshold $c \in \mathbb{R}$, the CUSUM alarm time is

$$N_c = \inf\{n \ge 1 : W_n \ge c\},$$

where $W_n$ is [Page's CUSUM statistic](page-cusum.md), with $N_c = \infty$ if no alarm is raised (Veeravalli–Banerjee, equation (43)).

## Sources

- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §IV, equations (43) and (48).
- T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica 11 (2001) 303–408, §3, equation (3.1).
