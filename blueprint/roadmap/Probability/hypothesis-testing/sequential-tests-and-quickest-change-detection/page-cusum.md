# Page's CUSUM statistic

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. Page's CUSUM statistic is defined by $W_0 = 0$ and

$$W_{n+1} = \max\big(W_n + \log L(X_{n+1}),\ 0\big)$$

(Veeravalli–Banerjee, equation (45)).

## Sources

- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §IV, equations (43)–(45), crediting E. S. Page (1954).
