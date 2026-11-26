# Runtime density of tau-splitting

**Setting.** For a stochastic reaction network simulated by the [exact tau-splitting algorithm](exact-tau-splitting-algorithm.md), a **runtime density** is a function $f$ on states such that the expected running time equals the expected integral $\mathbb{E}\int_0^T f(S_t)\,dt$ along the trajectory. Reaction $R_i$ **depends** on $R_j$ if some input species $k \in I_i$ has $O_j[k] \ne 0$. Let $D_i$ be the number of reactions that depend on $R_i$ or on which $R_i$ depends, let $\rho_i(S)$ be the rate of $R_i$, and let $\rho_k^{\pm} = \sum_j \rho_j(S)\,|O_j[k]|$ be the total rate at which species $k$ changes.

**Statement.** When all counts $S[k]$ are sufficiently large,

$$f(S) = O\Bigg(\sum_i D_i \sqrt{\rho_i(S) \sum_{k \in I_i} \frac{\rho_k^{\pm}}{S[k]}}\Bigg)$$

is a runtime density for the (full) tau-splitting algorithm. By comparison, exact event-by-event methods such as RSSA-CR have runtime density $O\big(\sum_i (D_i' + K)\rho_i(S)\big)$, linear in the total firing rate ($D_i'$ the number of reactions depending on $R_i$, $K$ the number of rate groups). Since $\rho_k^{\pm}/S[k]$ is the relative rate of change of species $k$, tau-splitting scales like the square root of the firing rate times the relative drift, which is much smaller than the firing rate for abundant species.

## Depends on

- [Exact tau-splitting algorithm for the chemical master equation](exact-tau-splitting-algorithm.md)

## Expansion

On a segment of length $t$, reaction $R_i$ fires about $\rho_i t$ times, so its Poisson-coupling interval $[l_i, u_i)$ has relative width about $1/\sqrt{\rho_i t}$ around $\rho_i$, while its rate drifts by a relative amount about $t\sum_{k\in I_i}\rho_k^{\pm}/S[k]$. The step is accepted once the drift is below the interval width, that is at segment length $t^\ast \asymp \big(\rho_i \sum_{k \in I_i} \rho_k^{\pm}/S[k]\big)^{-1/2}$, and processing $R_i$ in one recursive step costs $O(D_i)$. Summing the work per unit time $D_i/t^\ast$ over the dyadic segments, with a separate bound for the rare segments where a count could drop below the change it undergoes, gives the density.

## Sources

- R. Solan and G. Getz, An exact tau-leaping method, arXiv (2025). <https://doi.org/10.48550/arXiv.2509.12631> (Theorem 2.2, restated in technical form as Theorem 4.4; Lemmas 2.1, 4.7 to 4.11.)
