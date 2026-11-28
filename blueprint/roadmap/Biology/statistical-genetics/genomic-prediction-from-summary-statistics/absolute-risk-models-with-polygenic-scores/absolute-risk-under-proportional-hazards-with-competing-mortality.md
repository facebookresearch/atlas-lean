# Absolute risk under proportional hazards with competing mortality

Let $Z = (Z_1, \dots, Z_K)$ be an individual's risk factors (genetic scores, environmental exposures and interaction terms). Assume the age-specific disease incidence (hazard) follows the proportional hazards model

$$I(a \mid Z) = I_0(a)\exp\Big(\sum_{k=1}^{K}\beta_k Z_k\Big),$$

with baseline hazard $I_0$ and hazard ratios $e^{\beta_k}$; $\exp(\sum_k\beta_k Z_k)$ is the **multivariate relative risk**. Let $m(v \mid Z)$ be the hazard of death from other causes. For a person disease-free and alive at age $a$, the **absolute risk** of developing the disease in the age interval $[a, a+s]$ is

$$R_{a, a+s}(Z) = \int_a^{a+s} I(u \mid Z)\exp\Big(-\int_a^u \big\{I(v \mid Z) + m(v \mid Z)\big\}\,dv\Big)\,du .$$

It is the cumulative incidence of disease in the presence of the competing risk of death: the probability of developing the disease at age $u$ having remained free of both disease and death until $u$, integrated over the interval.

When relative risks are estimated from cohort or case–control studies and the overall population incidence $\bar I(a)$ is known from registries, the baseline hazard is recovered from the fact that $\bar I(a)$ is the average of the covariate-specific incidence over the distribution $F_a$ of risk factors in the at-risk population at age $a$, that is, among members of the underlying population who are disease-free and alive at age $a$ (not the whole population): $\bar I(a) = I_0(a)\int\exp\big(\sum_k\beta_k z_k\big)\,dF_a(z)$. For a relatively rare disease with fixed risk factors (such as SNPs) that have modest effects on disease and competing mortality, $F_a$ can be taken to be constant in $a$.

## Remarks

Treat disease onset and death from other causes as competing events with cause-specific hazards $I(\cdot \mid Z)$ and $m(\cdot \mid Z)$. The probability of being event-free from $a$ to $u$ is $\exp(-\int_a^u (I + m)\,dv)$, and the density of a disease event at $u$ among those event-free is $I(u \mid Z)$; integrating their product gives $R_{a,a+s}$. Ignoring $m$ (setting it to $0$) gives $1 - \exp(-\int_a^{a+s} I\,dv)$, which overstates risk at older ages where competing mortality is high. Because the hazard enters both the integrand and the survival factor, absolute risk is increasing but not linear in the relative risk, so two people with the same relative risk can face very different absolute risks depending on age and baseline incidence; this is what decides whether risk stratification changes a screening or prevention decision.

## Sources

- N. Chatterjee, J. Shi and M. García-Closas, "Developing and evaluating polygenic risk prediction models for stratified disease prevention", *Nature Reviews Genetics* 17 (2016), 392–406, Box 1 ("Incidence-based model for absolute risk of diseases") and section on estimating absolute risk, <https://doi.org/10.1038/nrg.2016.27> (PMC6021129).
