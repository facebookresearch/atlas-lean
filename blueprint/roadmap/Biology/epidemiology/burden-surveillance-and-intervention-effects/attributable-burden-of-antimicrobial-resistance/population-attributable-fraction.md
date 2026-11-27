# Population attributable fraction

**Setting.** A binary exposure has prevalence $p \in [0,1]$ in a population. Unexposed individuals have outcome risk $r_0 > 0$ and exposed individuals have risk $\mathrm{RR}\cdot r_0$, with relative risk $\mathrm{RR} > 0$ interpreted causally. The population attributable fraction (PAF) is the proportional reduction in outcomes if exposure were removed (counterfactual: everyone unexposed):

$$\mathrm{PAF} = \frac{r_{\mathrm{pop}} - r_0}{r_{\mathrm{pop}}}, \qquad r_{\mathrm{pop}} = (1-p)\,r_0 + p\,\mathrm{RR}\,r_0 .$$

**Proposition.**

1. (Levin's formula) $\displaystyle \mathrm{PAF} = \frac{p(\mathrm{RR} - 1)}{1 + p(\mathrm{RR} - 1)}$.
2. (Case-based form) If $p_c$ is the prevalence of exposure among cases, then $\displaystyle \mathrm{PAF} = p_c\,\frac{\mathrm{RR} - 1}{\mathrm{RR}}$.
3. If $\mathrm{RR} \ge 1$ then $0 \le \mathrm{PAF} \le p_c$, with equality on the right only when $p_c = 0$; $\mathrm{PAF}/p_c = (\mathrm{RR} - 1)/\mathrm{RR}$ tends to $1$ as $\mathrm{RR} \to \infty$ without reaching it.

## Remarks

Item 1 follows by substituting $r_{\mathrm{pop}}$ and dividing by $r_0$. For item 2, the fraction of cases that are exposed is $p_c = p\,\mathrm{RR}/(1 + p(\mathrm{RR}-1))$; multiplying by $(\mathrm{RR}-1)/\mathrm{RR}$ recovers item 1. Item 3 is immediate from item 2 since $(\mathrm{RR}-1)/\mathrm{RR} \in [0,1)$. The case-based form is the one usable when exposure prevalence is observed among deaths, as in burden studies.

## Sources

- M. L. Levin, *The occurrence of lung cancer in man*, Acta Unio Int. Contra Cancrum 9 (1953), 531–541.
- O. S. Miettinen, *Proportion of disease caused or prevented by a given exposure, trait or intervention*, Am. J. Epidemiol. 99 (1974), 325–332. <https://doi.org/10.1093/oxfordjournals.aje.a121617>
- GBD 2021 Antimicrobial Resistance Collaborators, *Global burden of bacterial antimicrobial resistance 1990–2021: a systematic analysis with forecasts to 2050*, Lancet 404 (2024). <https://doi.org/10.1016/S0140-6736(24)01867-1> (PMCID: PMC11718157). Methods, "Forecasting AMR population attributable fractions".
