# Combining sequenced and imputed association statistics: effective sample size $n + r^2 m$

Suppose a variant is tested in $n$ sequenced individuals and, separately, in $m$ individuals whose genotypes are imputed with squared correlation $r^2 \in (0, 1]$ between imputed dosage and true genotype. Assume the two statistics are independent with

$$Z_n^{\mathrm{seq}} \sim N(\eta \sqrt n, 1), \qquad Z_m^{\mathrm{imp}} \sim N(\eta \sqrt{r^2 m}, 1),$$

where $\eta$ is an effect-size parameter ($\eta = 0$ under the null). Define the sample-size weighted meta-analysis statistic

$$Z_{nm} = c_{nm}^{1/2} Z_n^{\mathrm{seq}} + (1 - c_{nm})^{1/2} Z_m^{\mathrm{imp}}, \qquad c_{nm} = \frac{n}{n + r^2 m}.$$

Then $Z_{nm} \sim N\bigl(\eta \sqrt{n + r^2 m}, 1\bigr)$, so the combined design has the power of a fully sequenced study of $n + r^2 m$ individuals. Among all statistics $a Z_n^{\mathrm{seq}} + b Z_m^{\mathrm{imp}}$ with $a^2 + b^2 = 1$ this choice maximizes the mean, and the two-sided level-$\alpha$ power is

$$1 - \int_{-z_{1-\alpha/2}}^{z_{1-\alpha/2}} \phi\bigl(u - \eta\sqrt{n + r^2 m}\bigr)\, du.$$

## Expansion

The variance is $c + (1 - c) = 1$ and the mean is $\eta(\sqrt{c n} + \sqrt{(1 - c) r^2 m}) = \eta (n + r^2 m)/\sqrt{n + r^2 m}$. By Cauchy–Schwarz, $a\sqrt n + b\sqrt{r^2 m} \le \sqrt{n + r^2 m}$ with equality for $(a, b) \propto (\sqrt n, \sqrt{r^2 m})$, which is the stated weighting. The modeling input is that imputation multiplies the noncentrality by $r$ (equivalently the effective sample size by $r^2$). Quick et al. average the power over variants with their empirical $r^2$ and set it to $0$ for variants that are not imputable.

## Sources

- C. Quick, P. Anugu, S. Musani et al., "Sequencing and imputation in GWAS: cost-effective strategies to increase power and genomic coverage across diverse populations", *Genetic Epidemiology* 44 (2020), <https://doi.org/10.1002/gepi.22326> (PMC7449570). Section 2.3, the combined statistic $Z_{nm}$ and the power formula.
