# Ancestry validation coefficient for expression differences

Let $e_{gs}$ be the normalized expression of gene $g$ in sample $s$, and $\theta_s \in [0,1]$ the genome-wide proportion of ancestry from population 1 ($\theta_s = 1$ for samples of population 1, $0$ for population 2, fractional for admixed samples). The validation model is

$$e_{gs} = a_g \theta_s + \nu_{gs} \ \ (\text{unadmixed samples}), \qquad e_{gs} = c\, a_g \theta_s + \nu_{gs} \ \ (\text{admixed samples}),$$

where $a_g$ is the mean expression difference between the two populations and $c$ is a single coefficient shared by all genes. Fitting by alternating least squares in $a_g$ and $c$, or equivalently by regressing per-gene admixed slopes $\tilde a_{g,\mathrm{adm}}$ on per-gene population differences $\tilde a_{g,\mathrm{pop}}$ with a sampling-error correction to $\sum_g \tilde a_{g,\mathrm{pop}}^2$, estimates the fraction $c$ of observed population differences that is heritable. With $\gamma_{gs}$ the local ancestry of sample $s$ at gene $g$, the cis–trans extension for admixed samples is

$$e_{gs} = c_{\mathrm{cis}}\, a_g \gamma_{gs} + c_{\mathrm{trans}}\, a_g \theta_s + \nu_{gs},$$

and the proportion of heritable population differences due to cis variants is $\pi_{\mathrm{cis}} = c_{\mathrm{cis}}/(c_{\mathrm{cis}} + c_{\mathrm{trans}})$. If $F$ is the proportion of expression variance due to population differences, the quantity comparable to $F_{ST}$ for an additive trait is $Q_{ST} = F/(2 - F)$.

## Expansion

If observed differences between the source populations were entirely genetic and additive, admixed individuals would show a linear dependence on ancestry with the same slope, giving $c = 1$; environmental or batch differences between source populations do not transmit to admixed individuals and pull $c$ below $1$. Noise in the admixed data does not bias the slope regression, but noise in $\tilde a_{g,\mathrm{pop}}$ inflates the denominator, which the correction removes. For $Q_{ST}$: writing $V_B$ and $V_W$ for between- and within-population variance, $F = V_B/(V_B + V_W)$ and $Q_{ST} = V_B/(V_B + 2V_W) = F/(2 - F)$, the factor $2$ reflecting two haploid genomes per individual. The source obtains $c = 0.43$ for 4,197 genes (versus $0.96$ for genotypes), $c_{\mathrm{cis}} = 0.05$, $c_{\mathrm{trans}} = 0.38$ and $\pi_{\mathrm{cis}} \approx 12\%$ in African Americans.

## Sources

- A. L. Price, N. Patterson, D. C. Hancks, S. Myers, D. Reich, V. G. Cheung and R. S. Spielman, "Effects of cis and trans genetic ancestry on gene expression in African Americans", *PLoS Genetics* 4 (2008), e1000294, Materials and Methods sections on the validation coefficient $c$, cis and trans ancestry, and the computation of $Q_{ST}$, <https://doi.org/10.1371/journal.pgen.1000294> (PMC2586034).
