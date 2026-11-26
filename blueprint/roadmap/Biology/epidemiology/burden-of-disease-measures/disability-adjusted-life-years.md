# Disability-adjusted life-years

For a cause of disease in a given population, time period and age group, let deaths at age $a$ number $d_a$ and let $L_a$ be the remaining life expectancy at age $a$ in a fixed reference life table. Years of life lost are

$$\mathrm{YLL} = \sum_{a} d_a L_a .$$

For each health state $s$ attributable to the cause, let $p_{a,s}$ be the number of prevalent cases in age group $a$ and $w_s \in [0,1]$ the disability weight of that state, with $w_s = 0$ for full health and $w_s = 1$ for a state equivalent to death. Years lived with disability over one year are

$$\mathrm{YLD} = \sum_{a}\sum_{s} p_{a,s}\, w_s ,$$

and the burden of the cause is

$$\mathrm{DALY} = \mathrm{YLL} + \mathrm{YLD},$$

in units of healthy life-years lost. DALYs are additive over causes, ages and populations, and are reported both as totals and as age-standardized rates per $10^5$.

## Depends on

- [Age-standardized rate](age-standardized-rate.md)

## Expansion

The construction puts fatal and non-fatal consequences on one scale by valuing a year lived in state $s$ as $1 - w_s$ healthy years, so a death at age $a$ costs $L_a$ and a year of illness costs $w_s$. Using a single reference life table rather than each population's own life expectancy makes the loss attributable to a death the same everywhere, which is a normative choice that keeps comparisons from rewarding populations whose life expectancy is already low. The prevalence form of $\mathrm{YLD}$ attributes to a year the disability actually experienced in it, in contrast with an incidence form that charges the whole future course of new cases to the year of onset; the two agree in a steady state. Disability weights come from valuation surveys and carry their own uncertainty, which, with uncertainty in prevalence and mortality, is propagated into the intervals reported with any DALY estimate.

## Sources

- GBD 2017 Inflammatory Bowel Disease Collaborators. The global, regional, and national burden of inflammatory bowel disease in 195 countries and territories, 1990-2017. *The Lancet Gastroenterology and Hepatology* 5:17-30 (2020), Methods. DOI <https://doi.org/10.1016/S2468-1253(19)30333-4>. PMCID PMC7026709.
