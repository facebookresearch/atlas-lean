# Restricting susceptible movement in the multi-strain SIS model

Let $\Omega \subset \mathbb R^n$ be a bounded domain with smooth boundary and outer normal $\vec n$. The multi-strain diffusive SIS model with $k$ strains and no co-infection is

$$\begin{aligned} \partial_t S &= d_S \Delta S + \sum_{i=1}^k \gamma_i I_i - \frac{S \sum_{i=1}^k \beta_i I_i}{S + \sum_{j=1}^k I_j}, \\ \partial_t I_i &= d_i \Delta I_i - \gamma_i I_i + \frac{\beta_i S I_i}{S + \sum_{j=1}^k I_j}, \qquad i = 1, \dots, k, \end{aligned}$$

in $\Omega \times (0, \infty)$, with $\partial_{\vec n} S = \partial_{\vec n} I_i = 0$ on $\partial\Omega$, positive Hölder continuous transmission and recovery rates $\beta_i, \gamma_i$ on $\overline\Omega$, diffusion rates $d_S \ge 0$, $d_i > 0$, and nonnegative initial data of total mass $N = \int_\Omega (S + \sum_i I_i)\,dx > 0$, which is conserved.

Let $R(x) = \max_i \beta_i(x)/\gamma_i(x)$ be the local reproduction function of the disease and $H^- = \{x \in \overline\Omega : R(x) < 1\} = \bigcap_i \{R_i < 1\}$ the common low-risk (safety) region of all strains; $H^- \neq \emptyset$ if and only if $\min_{\overline\Omega} R < 1$.

1. **Small susceptible movement.** If $H^- \ne \emptyset$, there is $M > 0$, independent of $d_S$, such that every coexistence endemic equilibrium (all $I_i > 0$) satisfies

$$\frac1M \le \frac{\sum_{i=1}^k I_i(x)}{d_S} \le M \qquad \text{for all } 0 < d_S < 1,\ x \in \Omega.$$

Thus the total infected population at equilibrium is of order $d_S$ and vanishes as the movement of susceptibles is restricted.

2. **Lock-down of susceptibles.** If $d_S = 0$, $d_i > 0$ for all $i$, and $\min_{\overline\Omega} R < 1$, then every positive classical solution satisfies $\|S(t, \cdot) - S^*\|_\infty + \sum_i \|I_i(t, \cdot)\|_\infty \to 0$ for some nonnegative $S^* \in C(\overline\Omega)$: all strains are eradicated.

3. **No common safety region.** For $k = 2$, if $R > 1$ on $\overline\Omega$, $R_1 - R_2$ changes sign (each strain has a nonempty region where it dominates), $\beta_1/\beta_2$ is constant and the rates are $C^2$, then for small $d_i = \varepsilon D_i$ a coexistence endemic equilibrium persists for all small $d_S > 0$ and converges, as $d_S \to 0$, to a positive limit. Restricting susceptible movement then need not reduce infection.

For one strain with $d_S = 0$ and $\min R_1 > 1$, the unique endemic equilibrium is $I_e = N/\int_\Omega \frac{R_1}{R_1 - 1}$, $S_e = I_e/(R_1 - 1)$, and it attracts every positive solution.

## Expansion

These results complement the [threshold dynamics](threshold-dynamics-of-the-multi-strain-diffusive-sis-model.md) of the same model, whose basic reproduction number does not depend on $d_S$. With $d_S = 0$ the $S$ equation is an ODE in each point; on the safety region the infected classes cannot sustain themselves locally, and the mass constraint couples the regions through the diffusing infected classes. The single-strain equilibrium follows from setting $\beta_1 S/(S + I) = \gamma_1$ pointwise, which gives $S = I/(R_1 - 1)$ with $I$ constant (Neumann problem $d_1 \Delta I = 0$), and fixing the constant by the total mass $N$.

## Sources

- Y. Lou and R. B. Salako, *Control strategies for a multi-strain epidemic model*, Bull. Math. Biol. 84 (2022), 10, <https://doi.org/10.1007/s11538-021-00957-6>, PMCID PMC8627176 (Theorems 2.3, 2.4, 2.5, 2.6 and 2.8).
