# Symmetric overdominance with linked deleterious sites

Consider a Wright–Fisher population of effective size $N_e$ with a diallelic multiplicative fitness scheme over $n$ sites: a genotype has fitness

$$f = \prod_{k=1}^{n} \big(1 + s_k h_k\big),$$

where $s_k$ is the selection coefficient of site $k$ and $h_k$ its dominance factor for the genotype carried ($h_k = 0$ for the ancestral homozygote, $h_k = h$ for the heterozygote, $h_k = 1$ for the derived homozygote; $s_k < 0$ is purifying selection). Split the genome into a **target region** of $m$ sites held under **symmetric overdominance**, meaning heterozygotes at those sites have $s_{\mathrm{bal}} > 0$ and both homozygotes $0$, and a **flanking region** whose sites evolve with $s_{\mathrm{nb}} \le 0$ and additive dominance $h = 1/2$, linked to the target at recombination rate $r$ per base pair and mutating at rate $\mu$ per site per generation. Symmetric overdominance holds the target sites at intermediate frequency indefinitely, so coalescence of a sample at the target is older than neutral and genealogies of flanking sites are stretched in proportion to their linkage.

Under this model, as the recombination distance to the target grows, the effect on flanking variation decays, and two opposing consequences appear at short distances: the density of polymorphic flanking sites falls, while the frequencies of the flanking variants that remain polymorphic, including deleterious ones, rise relative to a neutral or purely purifying-selection baseline. Increasing $r$ by an order of magnitude essentially removes both effects; decreasing it by the same factor strengthens them at every level of purifying selection.

## Depends on

- [Neutral Wright–Fisher transition matrix](../../wright-fisher-markov-chain/wright-fisher.md)
- [Directional selection, overdominance and underdominance at one locus](../../selection-migration-and-transmission/one-locus-selection-dynamics/one-locus-viability-selection-regimes.md)

## Expansion

Two lineages sampled on the same balanced haplotype can coalesce only when one of them recombines off it or when the allelic classes themselves coalesce, which under long-term balancing selection is far in the past; this lengthens local genealogies and raises the chance that a deleterious mutation drifts to intermediate frequency before purifying selection removes it, the "sheltered load" of a balanced polymorphism. The same old genealogy also means fewer independent mutational inputs survive as distinct segregating sites nearby, lowering polymorphic site density. Both effects are governed by the ratio of recombination rate to the rate at which lineages escape the balanced class, which is why they vanish with distance. Lenz et al. simulate this model with $N_e = 10{,}000$, $\mu = 1.38 \times 10^{-8}$, $r = 0.44$ cM/Mb, $s_{\mathrm{bal}} = 0.013$ at $117$ target sites and $s_{\mathrm{nb}}$ between $0$ and $-0.01$ in a $37$-kb flanking region, for $150{,}000$ generations after a $100{,}000$-generation burn-in at neutral equilibrium $\pi \approx 4N_e\mu$, and then confirm the prediction in exome data from about $6{,}500$ individuals: putatively deleterious coding variants in non-HLA genes of the MHC region segregate at elevated frequency, declining with physical distance from the classical HLA genes.

## Sources

- T. L. Lenz, V. Spirin, D. M. Jordan, S. R. Sunyaev, "Excess of deleterious mutations around HLA genes reveals evolutionary cost of balancing selection", Molecular Biology and Evolution 33 (2016), 2555–2564, <https://doi.org/10.1093/molbev/msw127> (PMC5026253), Results, "Simulating multilocus balancing selection", and Materials and Methods, "Forward simulation of balancing selection".
- A. Navarro, N. H. Barton, "The effects of multilocus balancing selection on neutral variability", Genetics 161 (2002), 849–863, <https://doi.org/10.1093/genetics/161.2.849>.
