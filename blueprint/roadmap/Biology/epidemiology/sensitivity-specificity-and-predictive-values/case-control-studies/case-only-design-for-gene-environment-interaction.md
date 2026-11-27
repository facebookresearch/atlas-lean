# Exact identities for the case-only odds ratio without gene–environment independence

Let $G$ and $E$ be binary exposures and $D$ a binary disease, and arrange a cohort as in a $2 \times 2 \times 2$ table with cases $a, c, e, g$ and non-cases $b, d, f, h$ in the cells $(G, E) = (0,0), (1,0), (0,1), (1,1)$, all positive. Let $S_{RR} = \mathrm{RR}_{ge}/(\mathrm{RR}_g \mathrm{RR}_e)$ be the [risk-ratio interaction](../../../not-yet-classified/case-only-interaction/risk-ratio-interaction.md) and $S_{OR} = \mathrm{OR}_{ge}/(\mathrm{OR}_g \mathrm{OR}_e)$ the [odds-ratio interaction](../../../not-yet-classified/case-only-interaction/odds-ratio-interaction.md), and write the cell risks as $r_{00} = a/(a+b)$, $r_{10} = c/(c+d)$, $r_{01} = e/(e+f)$ and $r_{11} = g/(g+h)$. With no independence assumption,

$$\frac{a g}{c e} = S_{RR} \cdot \frac{(g+h)(a+b)}{(c+d)(e+f)}, \qquad S_{OR} = S_{RR}\,\frac{(1 - r_{10})(1 - r_{01})}{(1 - r_{11})(1 - r_{00})}.$$

The first identity says that the case-only odds ratio equals the risk-ratio interaction times the population odds ratio of $G$ and $E$, so a $G$–$E$ association in the population can make the case-only design wrongly indicate a multiplicative interaction (VanderWeele, Hernández-Díaz and Hernán 2010). Under population independence it reduces to the [case-only odds ratio under population independence](../../../not-yet-classified/case-only-interaction/risk-ratio-interaction-eq-case-only.md), and the rare-disease agreement of $S_{OR}$ with $S_{RR}$ is the [rare-disease limit](../../../not-yet-classified/case-only-interaction/tendsto-odds-ratio-interaction-rare.md); neither is restated here.

## Depends on

- [Risk-ratio interaction](../../../not-yet-classified/case-only-interaction/risk-ratio-interaction.md)
- [Odds-ratio interaction](../../../not-yet-classified/case-only-interaction/odds-ratio-interaction.md)

## Expansion

1. The model: the cell masses, the risk ratios and odds ratios relative to the doubly unexposed cell, and the case-only odds ratio $ag/(ce)$.
2. The identity $ag/(ce) = S_{RR} \cdot (g+h)(a+b)/((c+d)(e+f))$, by writing each risk ratio through the cell totals.
3. The identity between $S_{OR}$ and $S_{RR}$, from $\mathrm{OR} = \mathrm{RR}\,(1 - r_{00})/(1 - r)$ for each exposed cell.
4. The relation between multiplicative statistical interaction and mechanistic interaction discussed in the source, as a separate statement.

## Sources

- T. J. VanderWeele, S. Hernández-Díaz and M. A. Hernán, Case-only gene–environment interaction studies: when does association imply mechanistic interaction?, Genet. Epidemiol. 34 (2010), 327–334, section on statistical interaction. <https://doi.org/10.1002/gepi.20484>
- Original result: W. W. Piegorsch, C. R. Weinberg and J. A. Taylor, Non-hierarchical logistic models and case-only designs for assessing susceptibility in population-based case-control studies, Stat. Med. 13 (1994), 153–162. <https://doi.org/10.1002/sim.4780130206>
