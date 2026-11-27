# Partitioned D-statistic for five-taxon introgression tests

**Setting.** Consider five taxa with assumed species tree $(((P_1, P_2), (P_{3_1}, P_{3_2})), O)$, where $P_{3_1}$ and $P_{3_2}$ are two lineages of the $P_3$ clade assumed not to exchange genes with each other, and $O$ is an outgroup carrying the ancestral allele $A$ at every biallelic site used. Write a site pattern as the states of $(P_1, P_2, P_{3_1}, P_{3_2}, O)$ with $B$ the derived allele, and let $n(\cdot)$ be the genome-wide count of sites with that pattern.

**Definition.** The partitioned D-statistics are

$$D_1 = \frac{n(ABBAA) - n(BABAA)}{n(ABBAA) + n(BABAA)}, \qquad D_2 = \frac{n(ABABA) - n(BAABA)}{n(ABABA) + n(BAABA)},$$

$$D_{12} = \frac{n(ABBBA) - n(BABBA)}{n(ABBBA) + n(BABBA)} .$$

$D_1$ uses derived alleles present in $P_{3_1}$ but not $P_{3_2}$, $D_2$ those present in $P_{3_2}$ but not $P_{3_1}$, and $D_{12}$ those shared by both.

**Properties.**

1. Without gene flow, under the multispecies coalescent the two discordant patterns in each pair arise with equal probability (incomplete lineage sorting is symmetric in $P_1$ and $P_2$), so $\mathbb{E}$ of each numerator is zero.
2. Gene flow between $P_2$ and $P_{3_1}$ alone makes $D_1$ positive while leaving $D_2$ near zero, separating introgression from $P_{3_1}$ from introgression from its relative $P_{3_2}$, which the four-taxon test $(P_1, P_2, P_{3_1}, O)$ cannot do because alleles shared by common descent of $P_{3_1}$ and $P_{3_2}$ also enter its counts.
3. $D_{12}$ indicates direction: alleles that arose in the common ancestor of $P_{3_1}$ and $P_{3_2}$ reach $P_2$ only by gene flow from the $P_3$ lineage into $P_2$, so a significant $D_{12}$ supports $P_3 \to P_2$ introgression and a non-significant $D_{12}$ together with a significant $D_1$ supports $P_2 \to P_{3_1}$.
4. If $P_{3_1}$ and $P_{3_2}$ are in fact not monophyletic relative to $P_1$ and $P_2$, they share no history independent of $P_1, P_2$ and $D_{12}$ is not expected to deviate from zero, which gives a test of the assumed $P_3$ clade.

## Depends on

- [The unpolarized D-statistic numerator vanishes on a tree](../../abba-baba-test-and-f-statistic-estimators/integral-sample-expect-abba-eq-baba.md)

## Expansion

Each partitioned statistic is a four-taxon ABBA–BABA comparison in which the "$P_3$" role is played by a particular configuration of the two $P_3$ lineages: present only in $P_{3_1}$, only in $P_{3_2}$, or in both. Under a tree without reticulation, the coalescent is exchangeable in $P_1$ and $P_2$ given that they are sisters, so each pair of patterns that differ by swapping the $P_1$ and $P_2$ states has equal expectation, as in the four-taxon D-statistic. Significance is assessed by a bootstrap over loci (resampling loci with replacement) to estimate the standard deviation of each $D$, and reporting $Z = D/\mathrm{sd}(D)$. With RAD-seq data, counts are summed over many short loci, so the statistic is a genome-wide average; sites heterozygous in any individual can be excluded to avoid phasing ambiguity.

## Sources

- Eaton DA, Ree RH, "Inferring phylogeny and introgression using RADseq data: an example from flowering plants (Pedicularis: Orobanchaceae)" (2013), Materials and Methods, "Partitioned D-statistic test" and "Directionality of gene flow", and Figure 3, <https://doi.org/10.1093/sysbio/syt032>, PMCID PMC3739883.
- K. J. Durand, N. Patterson, D. Reich and M. Slatkin, "Testing for ancient admixture between closely related populations", Molecular Biology and Evolution 28 (2011) 2239–2252, <https://doi.org/10.1093/molbev/msr048>.
