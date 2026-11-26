# Age-standardized rate

Let a population be divided into age groups $a = 1,\dots,A$, with $n_a$ persons and $d_a$ events observed in group $a$, giving age-specific rates $\rho_a = d_a/n_a$. Let $(w_a)_{a=1}^{A}$ be a fixed standard age structure with $w_a \ge 0$ and $\sum_a w_a = 1$. The directly age-standardized rate is the weighted mean

$$\mathrm{ASR} = \sum_{a=1}^{A} w_a \rho_a ,$$

reported per $10^5$ population by multiplying by $10^5$. The crude rate is the special case $w_a = n_a / \sum_b n_b$. Two populations compared through $\mathrm{ASR}$ computed with the same weights differ only through their age-specific rates: if $\rho_a \le \rho'_a$ for every $a$ then $\mathrm{ASR} \le \mathrm{ASR}'$, whatever the two age structures are.

## Expansion

The crude rate confounds risk with demography, so a population that is merely older can show a higher crude rate while every age-specific rate is lower. Fixing the weights removes that channel: the standardized rate is a counterfactual, the rate the population would show if its age distribution were the standard one. Consequently a divergence between the trend in case counts and the trend in the standardized rate is informative rather than contradictory, and is the usual signature of population growth and ageing acting on roughly stable age-specific risk. The value of $\mathrm{ASR}$ depends on the standard chosen, so only rates computed against the same standard are comparable, and uncertainty in the $\rho_a$ propagates linearly with weights $w_a$.

## Sources

- GBD 2017 Inflammatory Bowel Disease Collaborators. The global, regional, and national burden of inflammatory bowel disease in 195 countries and territories, 1990-2017. *The Lancet Gastroenterology and Hepatology* 5:17-30 (2020), Methods. DOI <https://doi.org/10.1016/S2468-1253(19)30333-4>. PMCID PMC7026709.
