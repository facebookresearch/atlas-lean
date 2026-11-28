# Liability variance explained by a rare null-allele burden

Let a gene carry rare alleles whose total population frequency is $f$, and suppose a fraction $\alpha \in (0, 1]$ of them are **null** (function-destroying) and the rest harmless, so the summed null-allele frequency is $q = \alpha f$. Model disease by a liability threshold: liability $\ell = \beta G + \varepsilon$, where $G \in \{0, 1, 2\}$ counts null alleles (Hardy–Weinberg proportions), $\beta$ is the effect of one null allele in standard-deviation units, $\varepsilon$ is an independent normal residual, and disease occurs when $\ell$ exceeds the threshold $T$ set by the prevalence $\kappa$. Then the fraction of liability variance explained by the burden is

$$V = \frac{2q(1 - q)\beta^2}{2q(1 - q)\beta^2 + \sigma_\varepsilon^2} \approx 2q(1-q)\beta^2 \quad (\text{liability variance normalized to } 1),$$

and the share of the heritability $h^2$ it accounts for is $V / h^2$. Given $\kappa$ and $\alpha$, the parameters $q$ and $\beta$ are fitted from the carrier counts in cases and controls: for rare alleles the carrier frequency in controls estimates the population frequency, and the case carrier frequency satisfies

$$P(\text{case} \mid \text{carrier}) = 1 - \Phi\bigl(T - \beta\bigr), \qquad P(\text{case}) = \kappa = 1 - \Phi(T),$$

to first order in $q$, with residual variance close to $1$.

**T1 burden test.** Collapse, within a gene, all qualifying variants (for example nonsynonymous, deleterious-predicted or disruptive) with sample minor allele frequency below $1\%$, and compare the number of carriers in cases and controls, with significance from phenotype permutations stratified by ancestry.

## Depends on

- [Case indicator of the threshold model](../../../liability-scale-heritability-from-ld-score-regre/case-ind.md)
- [Hardy–Weinberg proportions](../../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Expansion

For a biallelic locus with allele frequency $q$ and per-allele effect $\beta$, $\mathrm{Var}(\beta G) = \beta^2 \cdot 2q(1-q)$ under Hardy–Weinberg equilibrium, which gives $V$. A carrier (almost always heterozygous for rare alleles) has liability shifted by $\beta$, hence the case probability $1 - \Phi(T - \beta)$. The estimate is sensitive to $\alpha$: lumping harmless missense alleles with null ones dilutes the per-allele effect, so the same carrier enrichment implies a smaller $\beta$ on more alleles; the prevalence $\kappa$ matters less. For early-onset myocardial infarction (prevalence 3–5%), rare APOA5 alleles explained 0.08–0.17% and rare LDLR alleles 0.13–0.32% of liability variance, i.e. well under 1% of the heritability. Power calculations for the T1 test must account for the fact that oversampling cases and sampling noise push some causal alleles with population frequency below $1\%$ above the sample-frequency cutoff.

## Sources

- R. Do, N. O. Stitziel, H.-H. Won, A. B. Jørgensen, S. Duga, P. Angelica Merlini et al., "Exome sequencing identifies rare LDLR and APOA5 alleles conferring risk for myocardial infarction", Nature (2015), Methods "Rare Variant Association Analysis", "Estimation of Heritability Explained by a Burden of Rare Mutations in the APOA5 and LDLR Genes" and "Sample Size Extrapolations and Power Calculations for Burden of Rare Variants", <https://doi.org/10.1038/nature13917>, PMCID PMC4319990.
