# Genotype–allele equilibria under sex-linked segregation and the SDpop mixture

Consider a biallelic site with alleles $a, b$ in a large, randomly mating, diploid, dioecious population with an XY system (males heterogametic), and let $f \in [0,1]$ be the frequency of $a$ in the relevant copy. Genotypes are read as diploid calls $g \in \{aa, ab, bb\}$ after mapping reads to one reference locus. Under five segregation types the true genotype probabilities are:

- **Autosomal** (both sexes): $p(aa) = f^2$, $p(ab) = 2f(1-f)$, $p(bb) = (1-f)^2$ (Hardy–Weinberg).
- **Haploid** (both sexes): $p(aa) = f$, $p(ab) = 0$, $p(bb) = 1-f$.
- **Paralogous** (two non-recombining copies, one fixed for $b$): $p(aa) = 0$, $p(ab) = f^2 + 2f(1-f)$, $p(bb) = (1-f)^2$.
- **X-hemizygous**: females ($p_{\mathrm{f}}$) Hardy–Weinberg; males $p_{\mathrm{m}}(aa) = f$, $p_{\mathrm{m}}(ab) = 0$, $p_{\mathrm{m}}(bb) = 1-f$.
- **Gametologous XY**, X polymorphic with $b$ fixed on Y: females Hardy–Weinberg in $f$; males $p_{\mathrm{m}}(aa) = 0$, $p_{\mathrm{m}}(ab) = f$, $p_{\mathrm{m}}(bb) = 1-f$. Y polymorphic with $b$ fixed on X ($f$ the frequency of $a$ on Y): $p_{\mathrm{f}}(bb) = 1$; males $p_{\mathrm{m}}(aa) = 0$, $p_{\mathrm{m}}(ab) = f$, $p_{\mathrm{m}}(bb) = 1-f$.

The ZW cases follow by exchanging the sexes. **SDpop model.** Let $S$ be a latent segregation type in $\{\text{autosomal}, \text{haploid}, \text{paralogous}, \text{Xh}, \text{XY}, \text{Zh}, \text{ZW}\}$ with prior weights $\pi_S$, let $\rho_{XY}$ (resp. $\rho_{ZW}$) be the fraction of gametologous sites polymorphic on X (resp. Z), and let $e$ be a genotyping-error model giving $p(g \mid g')$. With $f$ replaced by its empirical plug-in value, each individual's observed genotype has

$$p(g \mid S) = \sum_{g'} p(g' \mid S)\, p(g \mid g'), \qquad p(g) = \sum_S \pi_S\, p(g \mid S),$$

and the likelihood is the product over individuals and sites. Parameters $(\pi, \rho, e)$ are fitted by EM; models (no sex linkage, XY, ZW, both) are compared by BIC with the number of polymorphic sites as sample size, and site types are assigned by empirical-Bayes posteriors $p(S \mid g)$.

## Remarks

Each row is a sampling identity. A hemizygous male carries one copy, so his diploid call is a homozygote in that allele. In a gametologous male the two copies are independent and one is monomorphic, so he is heterozygous exactly when the polymorphic copy carries the non-fixed allele. A paralog is a tetraploid locus with one copy fixed for $b$: the call is $ab$ unless the polymorphic copy is $bb$. The signature of sex linkage is therefore an asymmetry between the sexes, an excess of heterozygous males on XY gametologs and no heterozygous males at hemizygous sites, which an autosomal or paralogous site cannot produce. Because sites are treated as unlinked, gene-level scores use the geometric mean of site likelihoods with equal priors instead of the product. From the posterior subtype weights one gets X and Y allele frequencies $\hat f_X, \hat f_Y$, diversities $d_X = \langle 2\hat f_X(1-\hat f_X)\rangle$, $d_Y = \langle 2\hat f_Y(1-\hat f_Y)\rangle$ and divergence $D_{XY} = \langle \hat f_X(1-\hat f_Y) + \hat f_Y(1-\hat f_X)\rangle$.

## Depends on

- [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Sources

- J. Käfer, N. Lartillot, G. A. B. Marais and F. Picard, "Detecting sex-linked genes using genotyped individuals sampled in natural populations", Genetics 218 (2021), iyab053, Materials and methods ("Genotype frequencies", "Hierarchical structure of the model and likelihood function", "Parameter estimation and model comparison", "Haplotypes and population genetics inferences"), <https://doi.org/10.1093/genetics/iyab053>, PMCID PMC8225351.
