# Incremental cost-effectiveness ratio

Let $\mathcal{S}=\{s_1,\dots,s_m\}$ be competing control strategies for an epidemic model (for example single or combined optimal controls), each with total cost $C(s)$, taken from the objective functional evaluated along the optimal trajectory, and effectiveness $E(s)$, the number of infections averted relative to no control, $E(s)=\int_0^{T}\big(I_{\text{no control}}(t)-I_{s}(t)\big)\,dt$ or the analogous difference in cumulative cases. Order the strategies so that $E(s_1)<E(s_2)<\dots<E(s_m)$. The incremental cost-effectiveness ratio of $s_{j}$ against the next less effective strategy $s_{i}$ still in the list is

$$
\mathrm{ICER}(s_j)=\frac{C(s_j)-C(s_i)}{E(s_j)-E(s_i)},
$$

with $\mathrm{ICER}(s_1)=C(s_1)/E(s_1)$ measured against no control. The cost-effective frontier is obtained by repeated elimination:

1. **Strong dominance.** If $C(s_j)\le C(s_i)$ while $E(s_j)>E(s_i)$, so that $\mathrm{ICER}(s_j)\le 0$, then $s_i$ is dominated (costlier and less effective) and is removed.
2. **Extended dominance.** If $\mathrm{ICER}(s_i)>\mathrm{ICER}(s_j)$ for consecutive surviving strategies $s_i,s_j$, then $s_i$ is removed, since a mixture of its neighbours achieves the same effectiveness at lower cost.
3. Recompute the ICERs of the survivors and repeat until they increase strictly with $E$.

On the final list the ICERs are positive and increasing, and the preferred strategy is the most effective one whose ICER does not exceed the willingness to pay per infection averted. In the source's COVID-19 model with a preventive control $u_1$ and a case-management control $u_2$, the combined strategy averts the most infections at a lower cost than $u_2$ alone; the negative incremental ratio removes $u_2$, and the subsequent comparison with $u_1$ alone leaves the combined strategy as the most cost-effective.

## Expansion

Each ICER is the slope of the segment joining consecutive points in the (effectiveness, cost) plane. Strongly dominated strategies lie above and to the left of another point; extendedly dominated strategies lie above the segment joining their neighbours, so the surviving points form the lower convex hull of the cost-effectiveness plane, along which slopes increase. Infections averted depend on the time horizon and on whether the controls are optimized jointly or separately, so ICER rankings are conditional on the optimal-control formulation that produced the costs.

## Sources

- S. Olaniyi, O. S. Obabiyi, K. O. Okosun, A. T. Oladipo, S. O. Adewale, "Mathematical modelling and optimal cost-effective control of COVID-19 transmission dynamics", *The European Physical Journal Plus* 135 (2020) 938. <https://doi.org/10.1140/epjp/s13360-020-00954-z>. PMCID: PMC7688301. (Eq. (12), Tables 3–4.)
