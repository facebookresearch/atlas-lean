# Haley–Knott regression with additive and dominance effects

Consider a cross between two inbred lines $P_1$ and $P_2$ (or an introgression of $P_2$ segments into a $P_1$ background) and a putative QTL with genotypes $P_1P_1$, $P_1P_2$, $P_2P_2$. Code the QTL genotype of individual $i$ by the additive indicator $x_i \in \{-1, 0, 1\}$ and the dominance indicator $z_i \in \{0, 1, 0\}$ respectively, and model the phenotype as

$$y_i = \mu + a\,x_i + d\,z_i + \varepsilon_i, \qquad \varepsilon_i \sim \mathcal{N}(0, \sigma^2) \text{ i.i.d.}$$

The genotype means are $\mu - a$, $\mu + d$ and $\mu + a$; $a$ is the **additive effect** (half the homozygote difference) and $d$ the **dominance deviation** of the heterozygote from the homozygote midpoint, with dominance ratio $d/a$.

**Haley–Knott regression.** When the QTL genotype is not observed, replace $x_i$ and $z_i$ by their conditional expectations given the flanking marker genotypes $M_i$,

$$\tilde x_i = E[x_i \mid M_i], \qquad \tilde z_i = E[z_i \mid M_i],$$

computed from the recombination fractions between the QTL position and the markers, and fit $y_i = \mu + a \tilde x_i + d \tilde z_i + \varepsilon_i$ by least squares at each candidate position. The evidence for a QTL is the $F$- or likelihood-ratio statistic comparing this fit with the intercept-only model ($\chi^2_2$ asymptotically under normal errors); at a fully informative marker $\tilde x_i = x_i$, $\tilde z_i = z_i$ and the test is the marker-genotype ANOVA.

**Relative expression parametrization.** Measuring expression relative to the recipient genotype, i.e. setting the mean of $P_1P_1$ to $0$, forces $\mu = a$, so homozygous introgression genotypes have expected expression $2a$ and heterozygotes $a + d$. Applied to expression traits (eQTL), a divergently regulated gene linked to a marker near its own position is a cis-regulatory candidate, confirmed by allele-specific expression in heterozygotes, while a linked gene located elsewhere in the genome is trans-regulated.

## Depends on

- [Genotypic values at a biallelic locus on Falconer's scale](../fisher-s-decomposition-of-genetic-variance/biallelic-value.md)

## Expansion

The genotype means $\mu - a$, $\mu + d$, $\mu + a$ follow by substitution. Haley–Knott regression approximates the exact interval-mapping likelihood, a mixture of normals over the unobserved QTL genotype, by its first moment: $E[y_i \mid M_i] = \mu + a\tilde x_i + d\tilde z_i$ exactly, while the residual variance is inflated by the genotype uncertainty, which is small when markers are dense. It avoids the EM iterations of interval mapping and gives nearly identical LOD profiles. Significance thresholds across many traits and markers are set by false discovery rate control; in the Drosophila simulans–mauritiana introgression study, a nominal cutoff of $P = 2.1 \times 10^{-4}$ corresponded to FDR $0.02$ in males and $0.03$ in females, and divergent regulation was detected for 737 genes in males and 536 in females.

## Sources

- C. D. Meiklejohn, J. D. Coolon, D. L. Hartl and P. J. Wittkopp, "The roles of cis- and trans-regulation in the evolution of regulatory incompatibilities and sexually dimorphic gene expression", Genome Research (2014), Methods "Statistical analyses" and Results "Detecting divergent regulation in introgression genotypes", <https://doi.org/10.1101/gr.156414.113>, PMCID PMC3875864.
- C. S. Haley and S. A. Knott, "A simple regression method for mapping quantitative trait loci in line crosses using flanking markers", Heredity 69 (1992), 315–324, <https://doi.org/10.1038/hdy.1992.131>.
