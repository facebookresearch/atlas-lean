# Severity-weighted years lived with disability

Fix a location, a year and an age-sex stratum of population size $N$. Let a cause have severity levels $s = 1, \dots, S$ with prevalences $P_s \ge 0$ (counts of people) and disability weights $w_s \in [0,1]$, where $0$ is full health and $1$ is a state equivalent to death. The *unadjusted* years lived with disability of the cause are

$$\mathrm{YLD} \;=\; \sum_{s=1}^{S} P_s\, w_s ,$$

reported as the rate $100{,}000 \times \mathrm{YLD}/N$ per $100{,}000$ population and age-standardized as the [directly standardized rate](../../../population-dynamics/life-tables-and-direct-standardization/directly-standardized-rate-eq-crude-rate.md) of the age-specific rates under a fixed reference age structure.

For the comorbidity adjustment, let an individual carry a random set $\mathcal{C}$ of health states drawn independently across causes from their stratum-specific prevalences, with weights $(w_i)_{i \in \mathcal{C}}$. The combined disability of that individual is

$$w(\mathcal{C}) \;=\; 1 - \prod_{i \in \mathcal{C}} (1 - w_i),$$

with $w(\varnothing) = 0$ (the empty product is $1$). The combined disability is apportioned among the co-occurring states in proportion to their weights, so the amount charged to state $i \in \mathcal{C}$ is

$$a_i(\mathcal{C}) \;=\; w_i \cdot \frac{w(\mathcal{C})}{\sum_{i' \in \mathcal{C}} w_{i'}} \quad \text{when } \sum_{i' \in \mathcal{C}} w_{i'} > 0,$$

and $a_i(\mathcal{C}) = 0$ when every weight in $\mathcal{C}$ is $0$ (then $w(\mathcal{C}) = 0$ as well, so nothing is lost by this convention).

The comorbidity-adjusted $\mathrm{YLD}$ of a cause is $N\,\mathbb{E}\bigl[\sum_{i \in \mathcal{C} \cap \text{cause}} a_i(\mathcal{C})\bigr]$, estimated by simulating the joint distribution of health states.

**Monotonicity.** For every finite $\mathcal{C}$ with weights in $[0,1]$,

$$\max_{i \in \mathcal{C}} w_i \;\le\; w(\mathcal{C}) \;\le\; \min\Bigl(1, \sum_{i \in \mathcal{C}} w_i\Bigr),$$

and $w(\mathcal{C}) = \sum_{i \in \mathcal{C}} w_i$ exactly when at most one weight in $\mathcal{C}$ is positive. The right inequality is strict when no weight equals $1$ and at least two weights are positive; it can be an equality otherwise, for example for weights $(1, \tfrac12, \tfrac12)$, where $w(\mathcal{C}) = 1 = \min(1, 2)$. Hence $a_i(\mathcal{C}) \le w_i$, and the comorbidity-adjusted $\mathrm{YLD}$ of a cause never exceeds its unadjusted $\mathrm{YLD}$, with equality exactly when, almost surely, no positive-weight state of the cause co-occurs with another positive-weight state.

## Depends on

- [Directly standardized rate is the crude rate with the standard's sizes](../../../population-dynamics/life-tables-and-direct-standardization/directly-standardized-rate-eq-crude-rate.md)

## Remarks

The product form is the statement that disabilities compose on the *remaining health* scale: a state with weight $w$ leaves the fraction $1 - w$ of full health, and independent states multiply those fractions, so the combined loss is $1 - \prod_i (1-w_i)$. Subadditivity follows by induction on $\lvert \mathcal{C} \rvert$: for two states, $1-(1-w_1)(1-w_2) = w_1 + w_2 - w_1 w_2 \le w_1 + w_2$, strictly when both weights are positive, and $\ge \max(w_1,w_2)$ because $w_1 w_2 \le \min(w_1,w_2)$. The bound $w(\mathcal{C}) \le 1$ holds because every factor $1 - w_i$ lies in $[0,1]$, and $w(\mathcal{C}) < 1$ when no weight is $1$; combined with strict subadditivity this gives the strict inequality under the stated condition. Without such a rule, a person with many conditions could be assigned more than one year of disability per year lived, and cause-specific burdens would not sum to a coherent total.

Severity splitting precedes weighting because disability weights are defined for health states, not for diseases: the severity distribution is estimated from sources that grade the condition on a clinical index, and each level carries its own weight derived from population surveys that ask respondents to compare pairs of health state descriptions. Prevalence itself is produced by a Bayesian meta-regression over heterogeneous sources, with study-level covariates adjusting alternative case definitions onto the reference definition, and with nested random effects by super-region, region and country; the compartmental structure of that model enforces internal consistency between incidence and prevalence.

A caution from the same construction: when a cause is reported both per anatomical site and in total, counting one prevalent case per person per site makes the site-specific prevalences sum to more than the total, since a person affected at two sites is one case of the total but two site-specific cases.

## Sources

- GBD 2021 Osteoarthritis Collaborators, "Global, regional, and national burden of osteoarthritis, 1990-2020 and projections to 2050: a systematic analysis for the Global Burden of Disease Study 2021", The Lancet Rheumatology 5 (2023) e508-e522, Methods (severity distribution, disability weights, comorbidity-adjusted YLDs, DisMod-MR 2.1 meta-regression), <https://doi.org/10.1016/S2665-9913(23)00163-7> (PMC10477960).
