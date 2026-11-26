# Severity-weighted years lived with disability

Fix a location, a year and an age-sex stratum of population size $N$. Let a cause have severity levels $s = 1, \dots, S$ with prevalences $P_s \ge 0$ (counts of people) and disability weights $w_s \in [0,1]$, where $0$ is full health and $1$ is a state equivalent to death. The *unadjusted* years lived with disability of the cause are

$$\mathrm{YLD} \;=\; \sum_{s=1}^{S} P_s\, w_s ,$$

reported as a rate $\mathrm{YLD}/N$ per $100{,}000$ and age-standardized by averaging age-specific rates with the weights of a fixed reference age structure.

For the comorbidity adjustment, let an individual carry a random set $\mathcal{C}$ of health states drawn independently across causes from their stratum-specific prevalences, with weights $(w_i)_{i \in \mathcal{C}}$. The combined disability of that individual is

$$w(\mathcal{C}) \;=\; 1 - \prod_{i \in \mathcal{C}} (1 - w_i),$$

and the combined disability is apportioned among the co-occurring states in proportion to their weights, so the amount charged to state $i$ is

$$a_i(\mathcal{C}) \;=\; w_i \cdot \frac{w(\mathcal{C})}{\sum_{i' \in \mathcal{C}} w_{i'}} .$$

The comorbidity-adjusted $\mathrm{YLD}$ of a cause is $N\,\mathbb{E}\bigl[\sum_{i \in \mathcal{C} \cap \text{cause}} a_i(\mathcal{C})\bigr]$, estimated by simulating the joint distribution of health states.

**Monotonicity.** For every finite $\mathcal{C}$ with weights in $[0,1]$,

$$\max_{i \in \mathcal{C}} w_i \;\le\; w(\mathcal{C}) \;\le\; \min\Bigl(1, \sum_{i \in \mathcal{C}} w_i\Bigr),$$

with the right inequality strict as soon as two states with $w_i, w_{i'} \in (0,1)$ co-occur. Hence $a_i(\mathcal{C}) \le w_i$, and the comorbidity-adjusted $\mathrm{YLD}$ of a cause never exceeds its unadjusted $\mathrm{YLD}$, with equality only if the cause never co-occurs with another weighted state.

## Expansion

The product form is the statement that disabilities compose on the *remaining health* scale: a state with weight $w$ leaves the fraction $1 - w$ of full health, and independent states multiply those fractions, so the combined loss is $1 - \prod_i (1-w_i)$. Subadditivity follows by induction on $\lvert \mathcal{C} \rvert$: for two states, $1-(1-w_1)(1-w_2) = w_1 + w_2 - w_1 w_2 \le w_1 + w_2$, strictly when both weights are positive, and $\ge \max(w_1,w_2)$ because $w_1 w_2 \le \min(w_1,w_2)$. Without such a rule, a person with many conditions could be assigned more than one year of disability per year lived, and cause-specific burdens would not sum to a coherent total.

Severity splitting precedes weighting because disability weights are defined for health states, not for diseases: the severity distribution is estimated from sources that grade the condition on a clinical index, and each level carries its own weight derived from population surveys that ask respondents to compare pairs of health state descriptions. Prevalence itself is produced by a Bayesian meta-regression over heterogeneous sources, with study-level covariates adjusting alternative case definitions onto the reference definition, and with nested random effects by super-region, region and country; the compartmental structure of that model enforces internal consistency between incidence and prevalence.

A caution from the same construction: when a cause is reported both per anatomical site and in total, counting one prevalent case per person per site makes the site-specific prevalences sum to more than the total, since a person affected at two sites is one case of the total but two site-specific cases.

## Sources

- GBD 2021 Osteoarthritis Collaborators, "Global, regional, and national burden of osteoarthritis, 1990-2020 and projections to 2050: a systematic analysis for the Global Burden of Disease Study 2021", The Lancet Rheumatology 5 (2023) e508-e522, Methods (severity distribution, disability weights, comorbidity-adjusted YLDs, DisMod-MR 2.1 meta-regression), <https://doi.org/10.1016/S2665-9913(23)00163-7> (PMC10477960).
