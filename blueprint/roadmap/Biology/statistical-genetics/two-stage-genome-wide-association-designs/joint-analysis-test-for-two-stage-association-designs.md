# Joint analysis test for two-stage association designs

In a two-stage case–control design for $M$ markers, a fraction $\pi \in (0, 1)$ of the cases and controls is genotyped at all markers in stage 1, and only markers whose stage-1 allele-frequency statistic satisfies $|Z_1| > c_1$ are genotyped on the remaining fraction $1 - \pi$ in stage 2, giving an independent statistic $Z_2$. For equal per-individual information, the joint statistic is

$$Z_{\mathrm{joint}} = \sqrt{\pi}\,Z_1 + \sqrt{1 - \pi}\,Z_2 .$$

Under the null hypothesis of no association at a marker, $(Z_1, Z_{\mathrm{joint}})$ is asymptotically bivariate standard normal with correlation $\sqrt{\pi}$, and a marker is declared significant when $|Z_1| > c_1$ and $|Z_{\mathrm{joint}}| > c_2$. The marker-wise type I error is

$$\alpha = P\bigl(|Z_1| > c_1,\ |Z_{\mathrm{joint}}| > c_2\bigr),$$

so for a target $\alpha$ (for example $0.05/M$) and a chosen stage-1 threshold $c_1$, the joint threshold $c_2$ is found by solving this bivariate normal equation. The expected genotyping cost is $M\,n_1\kappa_1 + E[\#\{\text{markers passing stage 1}\}]\,n_2\kappa_2$, with $n_1, n_2$ the stage sample sizes and $\kappa_1, \kappa_2$ the per-genotype costs, and the design parameters ($\pi$, $c_1$, and, more generally, separate stage-1 fractions of cases and controls) are chosen to minimize cost at a required power or to maximize power at a fixed cost.

## Expansion

Each $Z_s$ is a standardized difference of case and control allele frequencies computed on independent individuals, so under the null $Z_1$ and $Z_2$ are independent standard normals and the combination with weights $\sqrt{\pi}, \sqrt{1-\pi}$ equals the statistic one would compute on all individuals at once. Joint analysis uses the stage-1 evidence again instead of discarding it, which is why it is more powerful than requiring replication in stage 2 alone. Allowing unequal proportions of cases and controls in stage 1, with information-weighted joint statistics, lowers cost further when controls outnumber cases or stage-2 genotyping is expensive.

## Sources

- S. A. Stanhope and A. D. Skol, "Improved minimum cost and maximum power two stage genome-wide association study designs", PLoS ONE 7 (2012) e42367, <https://doi.org/10.1371/journal.pone.0042367>, PMCID PMC3435377. Methods: stage-1 and stage-2 statistics, the joint test statistic, critical values, and the constrained cost and power optimization.
- A. D. Skol, L. J. Scott, G. R. Abecasis and M. Boehnke, "Joint analysis is more efficient than replication-based analysis for two-stage genome-wide association studies", Nature Genetics 38 (2006) 209–213, <https://doi.org/10.1038/ng1706>.
