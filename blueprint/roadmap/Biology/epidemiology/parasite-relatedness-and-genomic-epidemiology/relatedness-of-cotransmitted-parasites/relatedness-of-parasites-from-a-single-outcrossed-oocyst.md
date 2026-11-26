# Relatedness of parasites sampled from a single outcrossed oocyst

**Setting.** A haploid parasite reproduces sexually in the vector: two gametocytes fuse, the zygote undergoes one meiosis, and the resulting oocyst contains the four meiotic products in equal proportion. Sporozoites are then sampled from that pool, independently and with replacement, and each founds one infected hepatocyte in the next host. Define the relatedness of two parasites as the proportion of the genome that is identical by descent, that is, inherited from the same one of the original (mutually unrelated) parental strains.

**Proposition.** Consider one oocyst formed by outcrossing, with distinct parental strains $A$ and $B$, and two sporozoites drawn independently and uniformly from its four meiotic products. Then

$$\mathbb E[\text{relatedness}] = \frac{1}{4}\cdot 1 + \frac{3}{4}\cdot\frac13 = \frac12,$$

and conditional on the two draws being different meiotic products,

$$\mathbb E[\text{relatedness} \mid \text{different products}] = \frac13 .$$

The unconditional distribution is therefore bimodal, with an atom at $1$ (the same product drawn twice, that is, cotransmitted genetic clones, which do not create a mixed infection) and a mode near $1/3$ for pairs of distinct products. A pair of distinct products of one meiosis is related neither as full siblings nor as half siblings of the diploid classification; it forms its own kinship class, *meiotic siblings*, whose expected relatedness $1/3$ is item 3 of [Expected IBD relatedness of haploid parasite genealogies](../genealogical-relatedness-of-malaria-parasites/expected-ibd-relatedness-of-haploid-parasite-genealogies.md). In particular, a vector carrying exactly one oocyst can cotransmit only genetic clones or meiotic siblings, so every mixed infection it founds has expected relatedness $1/3$, whatever the number of infected hepatocytes; raising that number only concentrates the realized average around $1/3$.

## Proof depends on

- [Expected IBD relatedness of haploid parasite genealogies](../genealogical-relatedness-of-malaria-parasites/expected-ibd-relatedness-of-haploid-parasite-genealogies.md)

## Proof sketch

Fix a locus. The four chromatids of the bivalent at that locus comprise exactly two copies descended from $A$ and two from $B$, whatever the crossover configuration, because each crossover exchanges material between one chromatid of each homolog and so preserves the two-two split at every position. Two independent uniform draws from the four products agree in parental origin at that locus with probability

$$\frac14 + \frac34\cdot\frac{\binom{2}{2}+\binom{2}{2}}{\binom42} = \frac14 + \frac34\cdot\frac13 = \frac12,$$

the first term being the event that the same product is drawn twice. Relatedness is the average of this indicator over the genome, and expectation is linear, so the genome-wide expectations are the per-locus probabilities; no assumption about crossover numbers, interference or chromosome lengths is used. Conditioning on different products removes the first term and leaves $1/3$. Recombination controls the *spread* rather than the mean: with no crossovers each pair of distinct products is related $0$ or $1$ according to whether they descend from the same parent, while dense crossing over concentrates pairs near $1/3$ and $1$.

## Sources

- W. Wong, E. A. Wenger, D. L. Hartl, D. F. Wirth, *Modeling the genetic relatedness of Plasmodium falciparum parasites following meiotic recombination and cotransmission*, PLoS Computational Biology 14 (2018), e1005923, <https://doi.org/10.1371/journal.pcbi.1005923>, PMCID PMC5777656. Results, "Transmission model description" (four meiotic products per oocyst in equal proportion, sporozoite sampling, relatedness as the IBD proportion) and "Single oocyst simulations guarantee the transmission of meiotic siblings or genetic clones" (meiotic-sibling kinship class, simulated mean relatedness $0.5$ with modes at $1.0$ and $0.33$, expected relatedness $0.33$ of cotransmitted strains from a single oocyst, concentration with more infected hepatocytes). The per-locus two-two argument and the exact values $1/2$ and $1/3$ are derived here.
