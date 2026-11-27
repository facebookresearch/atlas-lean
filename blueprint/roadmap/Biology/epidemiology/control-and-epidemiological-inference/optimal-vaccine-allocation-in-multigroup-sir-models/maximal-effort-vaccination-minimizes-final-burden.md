# Maximal-effort vaccination minimizes final burden

**Model.** A population is split into groups $i = 1, \dots, n$ of sizes $N_i$ (total $1$), with compartments $S_i, I_i, R_i$ for people infected while unvaccinated and $S_i^V, I_i^V, R_i^V$ for vaccinated people. Doses are given at rate $U_i(t)$ to group $i$, with cumulative doses $W_i(t) = \int_0^t U_i$, and are assigned **at random among the not-yet-vaccinated** members of the group, so susceptibles are vaccinated at rate $U_i(t)\,S_i/(N_i - W_i(t))$:

$$\dot S_i = -\sum_j (\beta^1_{ij} I_j + \beta^2_{ij} I_j^V) S_i - \frac{U_i S_i}{N_i - W_i},\qquad \dot S_i^V = -\sum_j (\beta^3_{ij} I_j + \beta^4_{ij} I_j^V) S_i^V + \frac{U_i S_i}{N_i - W_i},$$

$$\dot I_i = \sum_j (\beta^1_{ij} I_j + \beta^2_{ij} I_j^V) S_i - \mu^1_i I_i,\quad \dot I_i^V = \sum_j (\beta^3_{ij} I_j + \beta^4_{ij} I_j^V) S_i^V - \mu^2_i I_i^V,\quad \dot R_i = \mu^1_i I_i,\quad \dot R_i^V = \mu^2_i I_i^V,$$

with vaccination "locally effective": vaccinated people transmit and are infected no more than unvaccinated ones in the same group, and recover no more slowly ($\mu^2_i \ge \mu^1_i > 0$). The classical model with vaccination term $U_i^* S_i$ is the special case $W_i = N_i(1 - e^{-\int_0^t U_i^*})$. The objective is the weighted final burden

$$H(U) = \sum_i p_i\big(R_i(\infty) + \kappa_i R_i^V(\infty)\big), \qquad 0 \le \kappa_i \le 1,$$

covering total infections or deaths, minimized over bounded integrable policies with $\sum_i U_i(t) \le A(t)$ (rate capacity) and $\sum_i W_i(t) \le B(t)$ (cumulative supply).

**Theorem (monotonicity).** If two feasible policies satisfy $\int_0^t U_i \le \int_0^t \tilde U_i$ for every group $i$ and all $t \ge 0$, then $H(U) \ge H(\tilde U)$: vaccinating more, sooner, in every group never increases the final weighted burden.

**Theorem (maximal effort is optimal).** Suppose $B$ is differentiable, an optimal policy exists, and the maximal achievable effort

$$\chi(t) = \begin{cases} A(t) & \text{if } \int_0^t \chi < B(t), \\ \min(A(t), B'(t)) & \text{if } \int_0^t \chi \ge B(t) \end{cases}$$

exists and is bounded. Then there is an optimal policy that uses the full effort, $\sum_i \tilde W_i(t) = \min\big(\int_0^t \chi, 1\big)$, and if $\chi$ is continuous almost everywhere, one with $\sum_i \tilde U_i(t) = \chi(t)$ until everyone is vaccinated. The same holds when a cost $F(W(\infty))$ of the doses used is added to the objective, with vaccination at full effort up to a stopping time $\tau$ and none afterwards.

## Expansion

Monotonicity is proved by comparing the two solutions componentwise: with more cumulative vaccination, at every time the unvaccinated susceptible pool is smaller and the combined "ever infected" counts $I_i + I_i^V + R_i + R_i^V$ end up no larger, although at a fixed finite time the better policy can transiently show more infections or deaths, which is why intuition alone does not settle the claim. The random-allocation model is what makes cumulative doses, rather than instantaneous rates, the natural control: giving a dose earlier is equivalent to raising $W_i$ at every later time. Optimality of maximal effort then follows by building, from an optimal policy, a full-effort policy whose cumulative doses are at least as large in every group, which by monotonicity is no worse. The result covers both mortality and infection objectives, but leaves open which group should receive the doses.

## Sources

- M. J. Penn, C. A. Donnelly, "Optimality of maximal-effort vaccination", Bulletin of Mathematical Biology (2023), model (1)–(5) and its reduction to the standard model (Eq 4), optimization problem (6), Theorems 1–3 and Propositions 1–2, <https://doi.org/10.1007/s11538-023-01179-8>, PMCID PMC10290047.
