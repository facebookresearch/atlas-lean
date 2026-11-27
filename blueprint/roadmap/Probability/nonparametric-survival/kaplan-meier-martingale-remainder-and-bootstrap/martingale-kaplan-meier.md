# Gill's Kaplan–Meier martingale in the two-coin censoring model

Consider the two-coin censoring model. The sample space is $\Omega_0 = \{\mathrm{true}, \mathrm{false}\}^2$ with all subsets measurable; a point is $\omega = (c, d)$, where $c$ is the censoring coin and $d$ the death coin. The measure $\mu_0$ gives mass $1/4$ to each of the four points. The filtration $(\mathcal F_n)_{n \in \mathbb N}$ has $\mathcal F_0 = \{\emptyset, \Omega_0\}$, $\mathcal F_1 = \sigma(c)$ (the preimages of subsets of $\{\mathrm{true}, \mathrm{false}\}$ under $\omega \mapsto c$) and $\mathcal F_n$ the power set for $n \ge 2$. The death process, the at-risk process and the cumulative hazard are

$$N_n(c, d) = \mathbf 1\{n \ge 2,\ c = \mathrm{false},\ d = \mathrm{true}\}, \qquad Y_n(c, d) = \mathbf 1\{n = 1 \text{ or } (n = 2 \text{ and } c = \mathrm{false})\}, \qquad \alpha_n = \begin{cases} 0, & n \le 1, \\ 1/2, & n \ge 2. \end{cases}$$

The Kaplan–Meier process and the product integral of the hazard are

$$\hat S_n(\omega) = \prod_{j < n} \Bigl(1 - Y_{j+1}(\omega)^{-1}\bigl(N_{j+1}(\omega) - N_j(\omega)\bigr)\Bigr), \qquad S_n = \prod_{j < n} \bigl(1 - (\alpha_{j+1} - \alpha_j)\bigr),$$

with the convention $0^{-1} = 0$, so a step with nobody at risk contributes the factor $1$.

The vanishing-risk remainder is

$$R_n(\omega) = \sum_{k < n} \frac{\hat S_k(\omega)}{S_{k+1}}\, \mathbf 1\{Y_{k+1}(\omega) = 0\}\, (\alpha_{k+1} - \alpha_k),$$

with real division ($x/0 = 0$).

Then the process

$$n \mapsto \frac{\hat S_n}{S_n} - 1 - R_n$$

is a martingale with respect to $(\mathcal F_n)$ under $\mu_0$: writing $Z_n = \hat S_n / S_n - 1 - R_n$, each $Z_n$ is $\mathcal F_n$-measurable, and $\mathbb E_{\mu_0}[Z_j \mid \mathcal F_i] = Z_i$ $\mu_0$-almost surely for all $i \le j$.

## Sources

- R. D. Gill, Censoring and Stochastic Integrals, Mathematical Centre Tracts 124, Amsterdam (1980), Section 3.2, Lemma 3.2.1(iv), (3.2.12) and (3.2.15)–(3.2.18), pp. 37–38 (the exponential and two-coin formulas are a specialization and a discrete analogue).
