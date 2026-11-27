# Attributable and associated burden of drug resistance

**Setting.** For an underlying cause of death $u$, infectious syndrome $\sigma$, pathogen $\pi$ and resistance profile $\varrho$, let $D_u$ be cause-specific deaths, $f^{\mathrm{sep}}_u$ the fraction of those deaths co-occurring with sepsis, $f_{\sigma \mid u}$ the fraction of sepsis deaths due to syndrome $\sigma$, $f_{\pi \mid \sigma}$ the fraction of syndrome deaths due to pathogen $\pi$, $\mathrm{PAF}_{\pi\varrho}$ the mortality [population attributable fraction](population-attributable-fraction.md) of resistance profile $\varrho$ against the counterfactual of a drug-*sensitive* infection, and $p_{\pi\varrho}$ the prevalence of $\varrho$ among deaths from $\pi$.

**Definitions.** Deaths attributable to resistance and deaths associated with resistant infection are

$$D^{\mathrm{attr}} = \sum_{u,\sigma,\pi,\varrho} D_u\, f^{\mathrm{sep}}_u\, f_{\sigma\mid u}\, f_{\pi\mid\sigma}\, \mathrm{PAF}_{\pi\varrho}, \qquad D^{\mathrm{assoc}} = \sum_{u,\sigma,\pi,\varrho} D_u\, f^{\mathrm{sep}}_u\, f_{\sigma\mid u}\, f_{\pi\mid\sigma}\, p_{\pi\varrho}.$$

The associated burden uses the counterfactual of *no infection*. Attributable [years lived with disability](../burden-of-disease-measures/severity-weighted-years-lived-with-disability.md) are the analogous product of syndrome incidence, pathogen fraction, disability per case and the non-fatal PAF, and attributable [DALYs](../burden-of-disease-measures/disability-adjusted-life-years.md) are the sum of attributable years of life lost and years lived with disability.

**Proposition.** If each $\mathrm{PAF}_{\pi\varrho}$ is given in the case-based form $p_{\pi\varrho}(\mathrm{RR}_{\pi\varrho} - 1)/\mathrm{RR}_{\pi\varrho}$ with relative risks $\mathrm{RR}_{\pi\varrho} \ge 1$ of death for resistant versus sensitive infection, then $0 \le D^{\mathrm{attr}} \le D^{\mathrm{assoc}}$.

## Depends on

- [Population attributable fraction](population-attributable-fraction.md)
- [Disability-adjusted life-years](../burden-of-disease-measures/disability-adjusted-life-years.md)
- [Severity-weighted years lived with disability](../burden-of-disease-measures/severity-weighted-years-lived-with-disability.md)

## Remarks

The two sums share all factors except the last, and termwise $0 \le \mathrm{PAF}_{\pi\varrho} \le p_{\pi\varrho}$ under the stated form, so the inequality holds summand by summand. The gap is the burden of resistant infections that would still have been fatal had the infection been drug-sensitive. For profiles resistant to several antibiotic classes the source reallocates burden to individual classes in proportion to excess risk, so that pathogen–drug burdens are mutually exclusive and sum to the total. It estimates 1.14 million attributable and 4.71 million associated deaths in 2021.

## Sources

- GBD 2021 Antimicrobial Resistance Collaborators, *Global burden of bacterial antimicrobial resistance 1990–2021: a systematic analysis with forecasts to 2050*, Lancet 404 (2024). <https://doi.org/10.1016/S0140-6736(24)01867-1> (PMCID: PMC11718157). Methods, "Computing burden attributable to drug resistance and burden associated with drug-resistant infections (step 10)".
