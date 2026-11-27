# Closed form of the CUSUM statistic

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. For every $n$ and $\omega$, [Page's CUSUM statistic](page-cusum.md) is the largest log-likelihood ratio of a final segment of the first $n$ observations:

$$W_n = \max_{0 \le j \le n} \sum_{i=j+1}^{n} \log L(X_i),$$

the empty segment ($j = n$) contributing $0$ (Veeravalli–Banerjee, equations (44)–(45)).

Equivalently $W_n = \Lambda_n - \min_{0 \le k \le n} \Lambda_k$, the excursion of the log-likelihood random walk above its running minimum (Veeravalli–Banerjee, (42)).

## Sources

- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §IV, equations (42)–(45).
