# Gene conversion and bacterial recombination in the ancestral graph

Gene conversion transfers a short tract of sequence instead of exchanging whole chromosome ends. Wiuf and Hein (2000, abstract) build a coalescent with intralocus gene conversion in which the tract length is geometric, derive a simulation scheme and analytical results, and give the expected number of topology shifts in a sample caused by conversion. In the ancestral process, as described by Baumdicker et al. (2022, section "Gene conversion"), conversion events are initiated at a rate per position along the genome with a geometrically distributed tract length, and a conversion extracts the tract of ancestry into an independent lineage, whereas a crossover splits ancestry to the left and right of a breakpoint. For bacteria, Vaughan et al. (2017, section "The ClonalOrigin genealogical model") describe the full coalescent with gene conversion, in which a conversion chooses its start site uniformly at random and its tract length from a geometric distribution, and the converted sites follow one parental lineage and the unconverted sites the other. The ClonalOrigin model they use labels lineages as clonal or non-clonal: non-clonal lineages neither convert nor coalesce with each other, given the clonal frame $C$ the number of conversions is Poisson with mean $\rho T\sum_{b}(L_b + \delta - 1)$, where $\rho$ is the per-site conversion rate, $\delta$ the expected tract length, $T$ the total branch length of $C$ and $L_b$ the length of locus $b$, and the locus, start site and end site of each conversion are drawn from the laws that enter the ClonalOrigin density, their equation (3). The ClonalOrigin model is a simplification of the coalescent with gene conversion, argued (following Didelot et al. 2010) to approximate it in the limit of small expected tract length, relative to genome length, and low recombination rate.

## Expansion

1. The gene-conversion event on ancestral material: initiation rate per position, geometric tract law, and extraction of the tract into a new lineage.
2. The ancestral graph with conversion and crossover, its non-explosion, and the Kingman law of the marginal genealogy at each position.
3. The expected number of topology shifts caused by conversion in a sample (Wiuf and Hein 2000).
4. The ClonalOrigin model: the density of a conversion set given the clonal frame (equation (3) of Vaughan et al.), and its relation to the full coalescent with gene conversion.

## Sources

- C. Wiuf and J. Hein, The coalescent with gene conversion, Genetics 155 (2000), 451–462, abstract. <https://doi.org/10.1093/genetics/155.1.451>
- F. Baumdicker et al., Efficient ancestry and mutation simulation with msprime 1.0, Genetics 220 (2022), iyab229, section "Gene conversion". <https://doi.org/10.1093/genetics/iyab229>
- T. G. Vaughan, D. Welch, A. J. Drummond, P. J. Biggs, T. George and N. P. French, Inferring ancestral recombination graphs from bacterial genomic data, Genetics 205 (2017), 857–870, section "The ClonalOrigin genealogical model" and equation (3). <https://doi.org/10.1534/genetics.116.193425>
- X. Didelot, D. Lawson, A. Darling and D. Falush, Inference of homologous recombination in bacteria using whole-genome sequences, Genetics 186 (2010), 1435–1449. <https://doi.org/10.1534/genetics.110.120121>
