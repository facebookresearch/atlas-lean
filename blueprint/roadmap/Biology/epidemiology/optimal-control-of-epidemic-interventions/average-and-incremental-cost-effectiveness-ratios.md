# Average and incremental cost-effectiveness ratios

**Setting.** A finite set of intervention strategies $s$ (for example single or combined optimal controls in an epidemic model) is evaluated over a fixed horizon against a common baseline (no intervention). For each strategy let $C_s \ge 0$ be its total cost and $E_s$ its total health effect, measured as infections (or cases, deaths) averted relative to the baseline, computed as the difference between baseline and controlled cumulative counts.

**Definitions.**
$$\mathrm{ACER}(s) = \frac{C_s}{E_s}, \qquad \mathrm{ICER}(s \mid s') = \frac{C_s - C_{s'}}{E_s - E_{s'}} \quad (E_s > E_{s'}),$$
the average cost per unit of effect against the baseline, and the extra cost per extra unit of effect when moving from the less effective strategy $s'$ to $s$.

**Ranking procedure.**

1. Order strategies by increasing effect $E_s$.
2. A strategy that costs at least as much as a more effective strategy is *strongly dominated* (negative or undefined ICER against it) and is removed.
3. Compute ICERs between successive remaining strategies, starting from the least effective (whose ICER equals its ACER). If the ICER sequence is not increasing, the strategy preceding a drop is *extendedly dominated*: a mixture of its neighbours achieves more effect at lower cost per unit. Remove it and recompute.
4. The remaining strategies form the efficient frontier, with strictly increasing ICERs; the most cost-effective choice for a willingness-to-pay $w$ per unit effect is the most effective frontier strategy with $\mathrm{ICER} \le w$.

## Expansion

ACER compares each strategy only to doing nothing, so it can favour a cheap but weak strategy; ICER compares adjacent options and measures the price of the additional benefit. The frontier is the lower convex hull of the points $(E_s, C_s)$: its slopes are the ICERs, and convexity is equivalent to the increasing-ICER condition, which is why extended dominance removes points lying above the hull. In optimal-control studies of epidemics the costs are typically $\int_0^T \sum_i B_i u_i^2\,dt$ from the [optimality system](pontryagin-optimality-system-with-quadratic-control-costs.md), and effects are averted infections.

## Depends on

- [Pontryagin optimality system with quadratic control costs](pontryagin-optimality-system-with-quadratic-control-costs.md)

## Sources

- A. Omame, H. Rwezaura, M. L. Diagne, S. C. Inyama, J. M. Tchuenche, "COVID-19 and dengue co-infection in Brazil: optimal control and cost-effectiveness analysis", The European Physical Journal Plus 136 (2021) 1090, Section 6 (cost-effectiveness analysis: ACER and ICER), <https://doi.org/10.1140/epjp/s13360-021-02030-6>.
- M. C. Weinstein, W. B. Stason, "Foundations of cost-effectiveness analysis for health and medical practices", New England Journal of Medicine 296 (1977) 716–721, <https://doi.org/10.1056/NEJM197703312961304>.
