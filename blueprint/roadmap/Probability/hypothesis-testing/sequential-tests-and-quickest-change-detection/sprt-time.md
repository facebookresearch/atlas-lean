# Wald's sequential probability ratio test

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. For log-boundaries $a, b \in \mathbb{R}$ (in practice $a < 0 < b$), the SPRT stops at

$$N = \inf\{n \ge 1 : \Lambda_n \le a \text{ or } \Lambda_n \ge b\},$$

with $N = \infty$ if this never happens, and accepts $P_1$ when $\Lambda_N \ge b$, $P_0$ when $\Lambda_N \le a$ (Lai 2001, equation (2.1), with $A = e^b$ and $B = e^a$).

In Lai's notation the test stops when $R_n = e^{\Lambda_n}$ leaves $(B, A)$ with $A > 1 > B > 0$; in the notation above $a = \log B$ and $b = \log A$. The Encyclopedia of Mathematics article writes the boundaries the other way round ($A < B$).

## Sources

- T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica 11 (2001) 303–408, §2, equation (2.1).
- B. Eisenberg, *Sequential probability ratio test*, Encyclopedia of Mathematics (online), equations (a1)–(a3).

## Background

- [Neyman–Pearson lemma](../neyman-pearson-dominated-two-simple.md): the fixed-sample-size likelihood-ratio test that the SPRT makes sequential.
