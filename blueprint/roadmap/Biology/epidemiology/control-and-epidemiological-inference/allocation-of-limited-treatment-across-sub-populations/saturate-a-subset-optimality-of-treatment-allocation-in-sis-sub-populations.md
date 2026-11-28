# Saturate-a-subset optimality of treatment allocation in SIS sub-populations

Consider $n$ independent sub-populations of sizes $N_i$, with infection confined within each. With time scaled so that the untreated recovery rate is $1$, the infected fraction obeys

$$\frac{dI_i}{dt} = \beta_i I_i(1 - I_i) - I_i - \eta_i \min(I_i, \gamma_i),$$

where $\beta_i > 1$ is the transmission rate, $\eta_i > 0$ the extra recovery rate from treatment, and $\gamma_i$ the largest treatable fraction. A budget $M$ is split once at $t = 0$ as $x_i M$ ($x_i \ge 0$, $\sum_i x_i = 1$), with per-host treatment cost $k_i$, so $\gamma_i = x_i M/(N_i k_i)$. The aim is to minimize the long-run burden $J = \sum_i N_i I_i^\infty$.

Let $C_0^{(i)} = 1 - 1/\beta_i$ (untreated endemic level) and $C_T^{(i)} = 1 - (1+\eta_i)/\beta_i$ (fully treated level). Sub-population $i$ is **saturated** if $I_i \to C_T^{(i)}$. When $I_i > \gamma_i$ throughout, the attracting equilibrium is

$$I_i^\infty = \tfrac12\Bigl(C_0^{(i)} + \sqrt{(C_0^{(i)})^2 - 4\eta_i\gamma_i/\beta_i}\Bigr).$$

**Minimal saturating treatment.** If $\eta_i < (\beta_i - 1)/2$, or if $I_i(0) < C_T^{(i)}$, it is $\gamma_C^{(i)} = C_T^{(i)}$. Otherwise the system is bistable and $\gamma_C^{(i)} = \frac{\beta_i}{\eta_i} I_i(0)\bigl(C_0^{(i)} - I_i(0)\bigr)$ for $C_T^{(i)} < I_i(0) \le C_0^{(i)}/2$, and $\gamma_C^{(i)} = \beta_i (C_0^{(i)})^2/(4\eta_i)$ for $I_i(0) > C_0^{(i)}/2$. The saturating cost therefore depends on initial prevalence.

**Theorem (structure of the optimum).** The objective has a unique interior critical point, $x_i^\star = a_i - b_i (\sum_j a_j - 1)/\sum_j b_j$ with $a_i = N_i (C_0^{(i)})^2 \beta_i k_i/(4\eta_i M)$ and $b_i = \eta_i N_i/(4M\beta_i k_i)$, and its Hessian has a negative eigenvalue, so it is not a minimum. Hence every optimal allocation saturates a subset $S$ of sub-populations, chosen so that the leftover $M_R = M - \sum_{i\in S} N_i k_i \gamma_C^{(i)}$ cannot saturate any other, and puts all of $M_R$ into a single remaining sub-population.

**Knapsack approximation.** Ignoring the leftover resource changes $J$ by at most $\tfrac12 C_0^{(m_0)} N_{m_0}$ for the sub-population $m_0$ receiving it, and choosing $S$ becomes the 0–1 knapsack problem

$$\max_S \sum_{i\in S} \bigl(C_0^{(i)} - C_T^{(i)}\bigr)N_i \quad \text{subject to} \quad \sum_{i\in S} k_i \gamma_C^{(i)} N_i < M,$$

with value $(C_0^{(i)} - C_T^{(i)})N_i$ (hosts saved) and weight $k_i\gamma_C^{(i)} N_i$ (cost to saturate).

## Expansion

Unsaturated burden $\tfrac12 N_i (C_0 + \sqrt{C_0^2 - c\,x_i})$ is concave in $x_i$, so a sum of such terms over the simplex is minimized at extreme points of each face. This is why spreading resources thinly is never optimal and why treatment should be focused. Saturation is a threshold: once $\gamma_i$ reaches $\gamma_C^{(i)}$ the burden drops to $C_T^{(i)} N_i$, a jump that rewards finishing one sub-population before starting another. In the bistable regime ($\eta_i > (\beta_i - 1)/2$) the backward-bifurcation-like structure of the constrained SIS model makes the saturating cost depend on initial prevalence, so identical sub-populations can need different budgets. In numerical tests over 50,000 parameter sets the knapsack rule had mean worst-case relative error $0.28\%$, and it outperformed allocating by size, by prevalence, or equally.

## Sources

- C. E. Dangerfield, M. Vyska, C. A. Gilligan, "Resource allocation for epidemic control across multiple sub-populations", Bulletin of Mathematical Biology (2019), Eqs. (1)–(3), (8)–(25), Table 2 and Appendix A, <https://doi.org/10.1007/s11538-019-00584-2>, PMCID PMC6491412.
