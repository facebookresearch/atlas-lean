# Case-only design for gene–environment interaction

Let $G$ and $E$ be binary exposures and $D$ a binary disease, and arrange a cohort as in a $2 \times 2 \times 2$ table with cases $a, c, e, g$ and non-cases $b, d, f, h$ in the cells $(G, E) = (0,0), (1,0), (0,1), (1,1)$. With the risk ratios $\mathrm{RR}_g$, $\mathrm{RR}_e$, $\mathrm{RR}_{ge}$ relative to the doubly unexposed cell, the multiplicative interaction on the risk-ratio scale is $S_{RR} = \mathrm{RR}_{ge}/(\mathrm{RR}_g \mathrm{RR}_e)$. If $G$ and $E$ are independent in the population, $(g + h)(a + b) = (c + d)(e + f)$, then

$$S_{RR} = \frac{a g}{c e},$$

the odds ratio relating $G$ and $E$ among cases, so a case-only study estimates the multiplicative interaction for risk ratios (Yang et al.; Schmidt and Schaid; as stated by VanderWeele, Hernández-Díaz and Hernán 2010). With the cell risks $r_{00} = a/(a+b)$, $r_{10} = c/(c+d)$, $r_{01} = e/(e+f)$ and $r_{11} = g/(g+h)$, the odds-ratio interaction of a case-control study, $S_{OR} = \mathrm{OR}_{ge}/(\mathrm{OR}_g \mathrm{OR}_e)$, satisfies $S_{OR} = S_{RR}\,\frac{(1 - r_{10})(1 - r_{01})}{(1 - r_{11})(1 - r_{00})}$, so the two coincide in the limit in which all four risks tend to $0$, the rare-disease case of Piegorsch et al. (1994). The identity follows from $S_{RR} = \frac{g/(g+h) \cdot a/(a+b)}{c/(c+d) \cdot e/(e+f)}$, in which the cell totals cancel by independence; when $G$ and $E$ are associated in the population, $ag/(ce)$ equals $S_{RR}$ times their population odds ratio $\frac{(g+h)(a+b)}{(c+d)(e+f)}$, and the design can then wrongly indicate a multiplicative interaction.

## Expansion

1. The model: the joint law of $(G, E, D)$, the risk ratios, and the case-only odds ratio.
2. The identity $S_{RR} = ag/(ce)$ under independence of $G$ and $E$, by cancellation of the cell totals.
3. The rare-disease approximation to the odds-ratio interaction.
4. The general formula with a $G$–$E$ association in the population, and the resulting bias.
5. The relation between multiplicative statistical interaction and mechanistic interaction discussed in the source, as a separate statement.

## Sources

- T. J. VanderWeele, S. Hernández-Díaz and M. A. Hernán, Case-only gene–environment interaction studies: when does association imply mechanistic interaction?, Genet. Epidemiol. 34 (2010), 327–334, section on statistical interaction. <https://doi.org/10.1002/gepi.20484>
- Original result: W. W. Piegorsch, C. R. Weinberg and J. A. Taylor, Non-hierarchical logistic models and case-only designs for assessing susceptibility in population-based case-control studies, Stat. Med. 13 (1994), 153–162. <https://doi.org/10.1002/sim.4780130206> The rare-disease approximation follows VanderWeele, Hernández-Díaz and Hernán (2010).
