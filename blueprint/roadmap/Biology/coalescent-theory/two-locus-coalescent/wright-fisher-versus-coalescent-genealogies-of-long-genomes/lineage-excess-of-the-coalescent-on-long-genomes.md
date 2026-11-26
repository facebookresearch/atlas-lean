# Lineage excess of the coalescent with recombination on long genomes

**Two models of one generation.** Follow the ancestry of a single haploid genome made of $c$ chromosomes with genetic lengths $\ell_1, \dots, \ell_c$ (in Morgans) back one generation in a diploid population of size $N$.

- *Discrete-time Wright–Fisher.* The genome was produced by one meiosis in one diploid parent, so its material traces to at most two parental haplotypes, however many crossovers occurred: successive crossovers switch back and forth between the same two lineages. Hence a sampled genome has at most $2^t$ ancestral haplotypes $t$ generations back, and the number of ancestral lineages of any sample never exceeds the haploid population size $2N$.
- *Hudson's coalescent with recombination.* Each lineage whose ancestral material spans genetic length $\ell$ splits at rate $\ell$ per generation, and each split creates a new, independent lineage; unlinked chromosomes are traced as separate lineages. Ignoring coalescence, the material of chromosome $k$ is carried after one generation by $1 + \mathrm{Poisson}(\ell_k)$ lineages, so the genome is carried by

$$c + \sum_{k=1}^{c} \mathrm{Poisson}(\ell_k)$$

lineages, with mean $c + \sum_k \ell_k$, instead of at most $2$.

For a human genome ($c = 22$ autosomes, total length about $35$ Morgans) this gives about $57$ ancestral lineages one generation back instead of $2$. In large samples the coalescent's lineage count can therefore exceed $2N$; in simulations of $10{,}000$ haploid genomes in a population of $10{,}000$ diploids it rose to about ten times $2N$ and stayed above $N_e$ for hundreds of generations, whereas the Wright–Fisher count never exceeds $2N$.

## Proof sketch

In Hudson's model a recombination at a point of a lineage's ancestral interval sends the left and right parts to two distinct ancestors chosen as if from an infinite population; without coalescence, breakpoints accumulate on each chromosome as a Poisson process of rate $t$ per Morgan, and every gap between breakpoints is its own lineage. The model is accurate for short regions, where two crossovers in one meiosis almost never fall in the region, and for small samples, where the extra lineages coalesce quickly. Over long regions it destroys the correlation that diploid inheritance imposes along the genome: two genomes sharing a recent ancestor should be identical by descent at several distant positions and on several chromosomes, and a recent migrant ancestor should leave migrant ancestry on several chromosomes. The excess lineages instead make nearly every sampled pair look like close relatives by local coalescence time while sharing too few long IBD segments. Simulating the first generations, where the sample is comparable to the population, with an explicit Wright–Fisher pedigree and switching to the coalescent once few lineages remain removes most of the bias.

## Depends on

- [Coalescent with recombination: ancestral-material state space and generator](../coalescent-with-recombination-ancestral-material.md)

## Sources

- D. Nelson, J. Kelleher, A. P. Ragsdale et al., "Accounting for long-range correlations in genome-wide simulations of large cohorts", PLoS Genetics 16 (2020), e1008619, <https://doi.org/10.1371/journal.pgen.1008619>, PMCID PMC7266353. Section "Motivation", Figures 1 and 2, and the discussion of hybrid simulations.
- R. R. Hudson, "Properties of a neutral allele model with intragenic recombination", Theoretical Population Biology 23 (1983), 183–201, <https://doi.org/10.1016/0040-5809(83)90013-8>.
