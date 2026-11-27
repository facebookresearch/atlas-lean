# Number needed to vaccinate with an added procedural risk

Consider a population in which an individual faces, over one year, a constant daily probability $D$ of acquiring an infection, with case fatality $C$ for that infection. Treating these as small independent per-day risks, the expected number of infection deaths per person-year is $365\,D\,C$, so the **number needed to vaccinate** to prevent one death, assuming a vaccine that removes that risk entirely, is

$$\mathrm{NNV}_{\text{community}} = \frac{1}{365\, D\, C}.$$

Now suppose the individual undergoes a procedure that adds a short window of elevated risk. Let $I$ be the probability of acquiring the infection within the $30$ days after the procedure and $R$ the mortality attributable to such a perioperative infection, the excess probability of death that the infection adds to the procedure's baseline risk; the procedure-attributable mortality is

$$S = I \cdot R.$$

Over the remaining $365 - 30 = 335$ days the individual carries the community risk, so the expected deaths per person-year become $S + 335\,D\,C$ and

$$\mathrm{NNV}_{\text{surgical}} = \frac{1}{S + 335\, D\, C}.$$

Since $S \ge 0$, $\mathrm{NNV}_{\text{surgical}} \le 1/(335 D C)$, and the two numbers differ substantially whenever $S$ is comparable with the annual community risk: the excess perioperative mortality $S$ replaces $30$ days of ordinary exposure and can dominate the sum, which is what makes a surgical population a priority group at a given community incidence. Both expressions are decreasing in $D$ and in $C$, so a higher prevailing incidence lowers both numbers, while the *ratio* $\mathrm{NNV}_{\text{community}}/\mathrm{NNV}_{\text{surgical}} = (S + 335DC)/(365DC)$ falls as incidence rises: the relative advantage of prioritizing surgical patients is largest when community incidence is low.

## Expansion

The formulas are first-order approximations in the per-day risks: the exact probability of avoiding infection over $n$ days is $(1 - D)^n$, and $1 - (1-D)^n \approx nD$ holds to within a relative error of order $nD$, which is a percent-level error for the daily incidences at which these calculations are used. They also assume the vaccine is fully protective, that the community risk is constant across the year, and that perioperative and community risks do not overlap — the first makes the computed number a lower bound on the true number needed, the last is handled crudely by shortening the community window to $335$ days. What the structure captures and a flat per-capita figure does not is that a time-limited hazard, however brief, enters additively on the same scale as a year of background exposure once it is expressed as an attributable mortality.

## Sources

- COVIDSurg Collaborative and GlobalSurg Collaborative, "SARS-CoV-2 vaccination modelling for safe surgery to save lives: data from an international prospective cohort study", British Journal of Surgery 108 (2021), 1056–1063, Methods (the two displayed NNV equations and $S = I \times R$), <https://doi.org/10.1093/bjs/znab101>, PMCID PMC7995808.
