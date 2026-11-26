# Incremental cost-effectiveness ratio of control strategies

**Setting.** Strategies $s = 1, \dots, K$ (single controls or combinations of controls in an optimally controlled epidemic model) each produce a total health effect $E_s \ge 0$ over the horizon, typically the number of infections averted relative to no intervention,

$$E_s = \int_0^{t_f} \big( I^{\mathrm{none}}(t) - I^{(s)}(t) \big)\, dt \quad \text{(or a cumulative-incidence analogue)},$$

and a total cost $C_s \ge 0$, typically $C_s = \int_0^{t_f} \sum_k \tfrac{b_k}{2}\, u_k^{(s)}(t)^2\, dt$ for the controls used by $s$.

**Definition.** Order the strategies by increasing effect, $E_{(1)} \le E_{(2)} \le \cdots$. The **incremental cost-effectiveness ratio** of a strategy relative to the next less effective one still in the comparison is

$$\mathrm{ICER}_{(i)} = \frac{C_{(i)} - C_{(i-1)}}{E_{(i)} - E_{(i-1)}}, \qquad \mathrm{ICER}_{(1)} = \frac{C_{(1)}}{E_{(1)}},$$

the extra cost per extra unit of effect.

**Elimination rule.** Repeat until no strategy is removed:
1. (*Strict dominance*) If $E_{(i)} \ge E_{(i-1)}$ and $C_{(i)} \le C_{(i-1)}$, with one inequality strict, so that $\mathrm{ICER}_{(i)} \le 0$, discard strategy $(i-1)$.
2. (*Extended dominance*) If $\mathrm{ICER}_{(i)} < \mathrm{ICER}_{(i-1)}$, discard strategy $(i-1)$: it buys effect at a higher marginal price than a more effective alternative.

The surviving strategies form the cost-effectiveness frontier with strictly increasing ICERs, and among them the first (least ICER) is the most cost-effective.

**Single-strategy summaries.** Two ratios compare each strategy only with no intervention: the **average cost-effectiveness ratio** $\mathrm{ACER}_s = C_s / E_s$ (cost per infection averted), and the **infection averted ratio** $\mathrm{IAR}_s = E_s / (\text{number recovered under } s)$, an effectiveness measure (larger is better). Ranking by ACER can disagree with the ICER frontier because ACER ignores what the next-cheaper alternative already achieves.

## Expansion

Plot each strategy as the point $(E_s, C_s)$. Strict dominance removes points lying above and to the left of another point. Extended dominance removes points lying above the segment joining their neighbours; after both removals the remaining points are the vertices of the lower convex hull of the cloud, which is why the frontier's incremental ratios increase. ICER values depend on the units of cost and effect and on the reference (usually the no-control scenario), and comparisons are meaningful only among strategies sharing the same horizon and cost model. In epidemic optimal-control studies the effects and costs are computed by solving the optimality system once per strategy, with the inactive controls fixed at zero.

## Depends on

- [Pontryagin optimality system for epidemic controls with quadratic costs](pontryagin-optimality-system-with-quadratic-control-costs.md)

## Sources

- F. B. Agusto and I. M. ELmojtaba, "Optimal control and cost-effective analysis of malaria/visceral leishmaniasis co-infection", PLoS ONE 12 (2017), e0171102, Section 6 (Eqs. (13)–(14), Tables 5–8), <https://doi.org/10.1371/journal.pone.0171102>, PMCID: PMC5293207.
- J. K. K. Asamoah, M. A. Owusu, Z. Jin, F. T. Oduro, A. Abidemi and E. O. Gyasi, "Global stability and cost-effectiveness analysis of COVID-19 considering the impact of the environment: using data from Ghana", Chaos, Solitons & Fractals 140 (2020), 110103, Section 4.2 (Eq. (21), Table 4), <https://doi.org/10.1016/j.chaos.2020.110103>, PMCID: PMC7351453.
- M. F. Drummond, M. J. Sculpher, K. Claxton, G. L. Stoddart and G. W. Torrance, *Methods for the Economic Evaluation of Health Care Programmes*, 4th ed., Oxford University Press (2015).
