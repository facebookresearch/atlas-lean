# Vaccinate a small vulnerable group first

**Model.** A population of total size $1$ is split into groups $i = 1, \dots, n$ of sizes $N_i$. Each group has unvaccinated $S_i, I_i, R_i$ and vaccinated $S_i^V, I_i^V, R_i^V$ classes, with transmission matrices $\beta^1, \beta^2, \beta^3, \beta^4$ (unvaccinated or vaccinated recipient $\times$ unvaccinated or vaccinated source, $\beta^1_{ij} \ge \beta^2_{ij}$, $\beta^3_{ij} \ge \beta^4_{ij}$) and recovery rates $\mu_i^1 \le \mu_i^2$:

$$\dot S_i = -\sum_j (\beta^1_{ij} I_j + \beta^2_{ij} I_j^V) S_i - \frac{U_i(t) S_i}{N_i - W_i(t)}, \qquad \dot S_i^V = -\sum_j (\beta^3_{ij} I_j + \beta^4_{ij} I_j^V) S_i^V + \frac{U_i(t) S_i}{N_i - W_i(t)},$$

with the usual infection and recovery equations, where $U_i(t) \ge 0$ is the vaccination rate in group $i$, $W_i(t) = \int_0^t U_i \le N_i$, and vaccines go to unvaccinated people at random. A policy is feasible if $\sum_i U_i(t) \le A(t)$ (rate cap) and $\sum_i W_i(t) \le B(t)$ (supply). The objective is the weighted final size

$$H(U) = \sum_{i=1}^n p_i\big(R_i(\infty) + \kappa_i R_i^V(\infty)\big), \qquad 0 \le \kappa_i \le 1.$$

**Theorem.** Let group 1 have size $N_1 = \epsilon$, initial susceptibles $\sigma\epsilon$ and infected $(1-\sigma)\epsilon$ with $\sigma \in (0,1)$, and cost weight $p_1 = 1/\epsilon$ (so the cost of infecting the whole group stays fixed), all other parameters fixed. Suppose group 1 can be infected by some other group $j$ with vaccine protection, $\beta^1_{1j} > \beta^3_{1j} \ge 0$, that every group except group 1 is infected in the $\epsilon = 0$ limit, and let $U(\cdot;\epsilon)$ be any family of policies with uniformly bounded finite support that, at some fixed time $\tau$, has vaccinated at least a fixed amount $w > 0$ in total but less than a fixed fraction $\alpha$ of group 1 ($W_1(\tau;\epsilon) < \alpha\epsilon$), with $|W_i(t;\epsilon) - W_i(t;0)| < \epsilon$. Let $\tilde U$ redirect all of $U$'s vaccines to group 1 until $\epsilon$ doses have been given and then follow $U$. Then $\tilde U$ is feasible and, for all sufficiently small $\epsilon$,

$$H(U(\cdot;\epsilon)) > H(\tilde U(\cdot;\epsilon)).$$

If moreover $\sigma = 1$ and the initial difference in force of infection on unvaccinated versus vaccinated members of group 1 is positive, then, if for each $\epsilon$ an optimal policy exists and these policies have uniformly bounded finite support, there is a sequence of optimal policies with $\lim_{\epsilon\to 0} \bar W_1(t;\epsilon)/\epsilon = 1$ whenever any vaccine has been available by time $t$: in the limit the vulnerable group is vaccinated as fast as possible.

## Expansion

Redirecting $\epsilon$ doses to group 1 changes the dynamics of the rest of the population only at order $\epsilon$, since group 1 is tiny and the other groups receive the same doses up to a shift of size $\epsilon$; by continuous dependence of the final size on the policy, the other groups' contribution to $H$ changes by $O(\epsilon)$. Group 1's contribution, however, is weighted by $1/\epsilon$: under $U$ a fixed fraction of group 1 stays unvaccinated through a period of $O(1)$ infection pressure from the other groups and is infected with probability bounded away from zero, contributing $O(1)$ to $H$; vaccinating it first removes a fixed fraction of that $O(1)$ term because vaccination lowers its force of infection ($\beta^1_{1j} > \beta^3_{1j}$). An $O(1)$ gain beats an $O(\epsilon)$ loss once $\epsilon$ is small. Numerically the threshold group size below which "vulnerable first" wins can be large, so the asymptotic rule is a guide for highly concentrated risk, such as age-concentrated mortality.

## Sources

- M. J. Penn, C. A. Donnelly, "Asymptotic analysis of optimal vaccination policies", Bulletin of Mathematical Biology 85 (2023) 15, Eqs. (8)–(21), Theorems 1–2 (Eqs. (30)–(43)) and Appendices A–B, <https://doi.org/10.1007/s11538-022-01114-3>, PMCID PMC9859927.
