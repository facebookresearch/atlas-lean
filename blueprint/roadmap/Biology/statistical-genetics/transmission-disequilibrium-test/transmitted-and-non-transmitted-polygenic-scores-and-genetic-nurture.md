# Transmitted and non-transmitted polygenic scores separate direct effects from genetic nurture

Let a child's outcome $Y$ depend linearly on the child's own polygenic score $C$ and on the polygenic scores $P_m, P_p$ of the mother and father:

$$Y = \delta\, C + \eta_m P_m + \eta_p P_p + \varepsilon,$$

where $\delta$ is the **direct genetic effect** and $\eta_m, \eta_p$ are **genetic nurture effects**, i.e. effects of parental genotype on the child's outcome through the environment the parent provides. Split each parent's score into the part on the haplotype transmitted to the child and the part on the non-transmitted haplotype, $P_m = T_m + N_m$ and $P_p = T_p + N_p$, so that $C = T_m + T_p$. Substituting,

$$Y = (\delta + \eta_m)\, T_m + \eta_m N_m + (\delta + \eta_p)\, T_p + \eta_p N_p + \varepsilon .$$

Two family designs identify the parameters from parent–offspring trios:

1. **Virtual parent (non-transmitted score) design.** The coefficient of a parent's non-transmitted score $N$ estimates that parent's genetic nurture effect $\eta$, and the difference between the transmitted and non-transmitted coefficients estimates $\delta$. A non-transmitted allele cannot reach the child genetically, so its association with $Y$ is not confounded by direct genetic transmission.
2. **Statistical control design.** Regressing $Y$ on $C$ together with $P_m$ and $P_p$ ("full control") recovers $\delta$ as the coefficient of $C$ and $\eta_m, \eta_p$ as the parental coefficients; controlling for only one parent's score ("partial control") leaves that parent's coefficient partly absorbing the other parent's effect through assortative mating.

Both rely on the same linear model; with random mating and no population structure the transmitted and non-transmitted haplotype scores of a parent are independent by random Mendelian segregation, so the decomposition can be estimated by ordinary least squares.

## Proof sketch

The decomposition is the identity $\delta C + \eta_m P_m + \eta_p P_p = \delta(T_m + T_p) + \eta_m(T_m + N_m) + \eta_p(T_p + N_p)$ regrouped by haplotype. Because Mendelian segregation decides at random which haplotype of each parent is transmitted, conditional on parental genotype the split into $T$ and $N$ is independent of family environment, which is what makes $N$ a clean instrument for the environmental path. Population stratification and assortative mating induce correlations among $T_m, N_m, T_p, N_p$ that bias the coefficients if a parent's score is omitted. A meta-analysis of 12 studies (38,654 offspring in 8 cohorts) using educational-attainment polygenic scores found a pooled genetic nurture effect of $\beta = 0.08$ (95% CI $0.07$–$0.09$) and a direct genetic effect of $\beta = 0.17$ (95% CI $0.13$–$0.20$) in standardized units, with no detectable difference between maternal and paternal genetic nurture.

## Sources

- B. Wang, J. R. Baldwin, T. Schoeler et al., "Robust genetic nurture effects on education: a systematic review and meta-analysis based on 38,654 families across 8 cohorts", The American Journal of Human Genetics 108 (2021), 1780–1791, Subjects and methods (eligibility designs "virtual parent" and "statistical control") and Results (Tables 2–3), <https://doi.org/10.1016/j.ajhg.2021.07.010> (PMC8456157).
