# Aalen's multiplicative intensity model holds in the two-coin censoring model

Consider the two-coin censoring model. The sample space is $\Omega_0 = \{\mathrm{true}, \mathrm{false}\}^2$ with all subsets measurable; a point is $\omega = (c, d)$, where $c$ is the censoring coin and $d$ the death coin. The measure $\mu_0$ gives mass $1/4$ to each of the four points. The filtration $(\mathcal F_n)_{n \in \mathbb N}$ has $\mathcal F_0 = \{\emptyset, \Omega_0\}$, $\mathcal F_1 = \sigma(c)$ (the preimages of subsets of $\{\mathrm{true}, \mathrm{false}\}$ under $\omega \mapsto c$) and $\mathcal F_n$ the power set for $n \ge 2$. The death process, the at-risk process and the cumulative hazard are

$$N_n(c, d) = \mathbf 1\{n \ge 2,\ c = \mathrm{false},\ d = \mathrm{true}\}, \qquad Y_n(c, d) = \mathbf 1\{n = 1 \text{ or } (n = 2 \text{ and } c = \mathrm{false})\}, \qquad \alpha_n = \begin{cases} 0, & n \le 1, \\ 1/2, & n \ge 2. \end{cases}$$

Let

$$A_n(\omega) = \sum_{k < n} Y_{k+1}(\omega)\,(\alpha_{k+1} - \alpha_k)$$

be the Aalen compensator. Then $M_n = N_n - A_n$ is a martingale with respect to $(\mathcal F_n)$ under $\mu_0$: each $M_n$ is $\mathcal F_n$-measurable, and $\mathbb E_{\mu_0}[M_j \mid \mathcal F_i] = M_i$ $\mu_0$-almost surely for all $i \le j$.

## Sources

- R. D. Gill, Censoring and Stochastic Integrals, Mathematical Centre Tracts 124, Amsterdam (1980), (3.1.5) and Assumption 3.1.2, pp. 25–26 (discrete-time compensator; the coin calculation is a discrete-time example). https://ir.cwi.nl/pub/12983/12983D.pdf
