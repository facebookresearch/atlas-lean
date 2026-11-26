# Cumulative PTV frequency at heterozygote mutation–selection balance

Treat a gene as a biallelic locus whose "mutant" state is the presence of any protein-truncating variant (PTV), with cumulative frequency $X \in [0,1]$ (the sum of PTV allele frequencies in the gene). Let $U > 0$ be the per-generation PTV mutation rate of the gene, and let $s_{\mathrm{het}} > 0$ and $s_{\mathrm{hom}} \ge 0$ be the fitness losses of heterozygous and homozygous (including compound heterozygous) carriers. Ignoring drift and back mutation, the deterministic dynamics are

$$\dot X = -s_{\mathrm{het}} X (1 - X) - s_{\mathrm{hom}} X^2 (1 - X) + U .$$

For $X \ll 1$ this reduces to

$$\dot X = F(X) := -s_{\mathrm{het}} X - s_{\mathrm{hom}} X^2 + U .$$

**Proposition.** On $[0, \infty)$ the reduced equation has the unique equilibrium

$$X^* = \begin{cases} \dfrac{-s_{\mathrm{het}} + \sqrt{s_{\mathrm{het}}^2 + 4 s_{\mathrm{hom}} U}}{2 s_{\mathrm{hom}}}, & s_{\mathrm{hom}} > 0, \\[2ex] \dfrac{U}{s_{\mathrm{het}}}, & s_{\mathrm{hom}} = 0, \end{cases}$$

which is globally asymptotically stable for initial conditions $X(0) \ge 0$, and satisfies

$$\frac{U}{s_{\mathrm{het}}} \Big(1 - \frac{s_{\mathrm{hom}} U}{s_{\mathrm{het}}^2}\Big) \le X^* \le \frac{U}{s_{\mathrm{het}}} .$$

Hence $X^* = U/s_{\mathrm{het}}$ up to a relative error at most $s_{\mathrm{hom}} U / s_{\mathrm{het}}^2$: when $s_{\mathrm{hom}} X^* \ll s_{\mathrm{het}}$, the equilibrium is set by selection against heterozygotes alone and does not depend on population size or demography. A sample of $N$ chromosomes then has expected PTV count $N X^* \approx N U / s_{\mathrm{het}}$, the [balance mean](balance-mean.md).

## Depends on

- [Mean PTV count at mutation-selection balance](balance-mean.md)
- [Mutation–selection balance in a haploid population](../../population-genetics/mutation-selection-balance/haploid-mutation-selection-balance.md)

## Expansion

$F$ is a concave quadratic (linear if $s_{\mathrm{hom}} = 0$) with $F(0) = U > 0$ and $F(X) \to -\infty$, so it has exactly one nonnegative root, given by the quadratic formula, and $F > 0$ below it and $F < 0$ above it; this sign pattern gives global stability on the half-line. Since $F(U/s_{\mathrm{het}}) = -s_{\mathrm{hom}} U^2 / s_{\mathrm{het}}^2 \le 0$ we get $X^* \le U/s_{\mathrm{het}}$. Then $s_{\mathrm{het}} X^* = U - s_{\mathrm{hom}} X^{*2} \ge U - s_{\mathrm{hom}} U^2 / s_{\mathrm{het}}^2$, which is the lower bound. The neglected factor $(1 - X)$ and drift are small when $X \le 10^{-3}$ and $4 N_e s_{\mathrm{het}} \gg 1$; Cassa et al. check the strong-selection regime $s_{\mathrm{het}} \gtrsim 10^{-3}$ by forward simulation under realistic human demographies and exclude genes with observed cumulative frequency above $10^{-3}$.

## Sources

- C. A. Cassa, D. Weghorn, D. J. Balick et al., "Estimating the selective effects of heterozygous protein-truncating variants from human exome data", Nature Genetics 49 (2017), Online Methods "Model of deterministic mutation-selection balance", Eqs. (1)–(3), <https://doi.org/10.1038/ng.3831>, PMCID PMC5618255.
