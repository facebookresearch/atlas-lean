# Tree-sequence inference and dating (tsinfer and tsdate)

tsinfer (Kelleher et al. 2019, Methods) infers a tree sequence from phased biallelic genotypes. Sites are ordered by a proxy for the age of the derived allele, by default its frequency; putative ancestral haplotypes are built around the derived allele at each site; and each ancestral haplotype is then matched, under a variant of the Li and Stephens copying model, as a mosaic of strictly older ancestral haplotypes, with a third haplotypic state for non-ancestral material from which no copying occurs. The most likely copying path is computed by the Viterbi algorithm, and the copying intervals become the edges of the tree sequence; the sample haplotypes are matched last against the ancestors. tsdate (Wohns et al. 2022) assigns ages to the nodes of any valid tree sequence by a Bayesian method; as summarized by Nielsen, Vaughn and Deng (2025, section 3.2), it estimates branch lengths from the distribution of mutations on branches under a coalescent prior. Neither step estimates a posterior over topologies: the review classes tsinfer with methods that infer a single topology.

## Expansion

1. The age ordering of sites and the construction of ancestral haplotypes.
2. The copying model against older ancestors, with the non-ancestral state, and the Viterbi path.
3. Validity of the output tree sequence (parents older than children in the age order; disjoint parent intervals) and compatibility of every site with mutations placed on its edges.
4. The dating model: a coalescent prior on node times, a Poisson likelihood for the mutation counts on edges, and the constraint that parents are older than children; the approximate posterior computation.
5. What the output does not establish: recovery of the true ancestral recombination graph or calibrated uncertainty for its topology.

## Sources

- J. Kelleher et al., Inferring whole-genome histories in large population datasets, Nat. Genet. 51 (2019), 1330–1338, Methods: "Inferring ancestral haplotypes" and "Copying process". <https://doi.org/10.1038/s41588-019-0483-y>
- A. W. Wohns et al., A unified genealogy of modern and ancient genomes, Science 375 (2022), eabi8264, Results and Fig. 1. <https://doi.org/10.1126/science.abi8264>
- R. Nielsen, A. H. Vaughn and Y. Deng, Inference and applications of ancestral recombination graphs, Nat. Rev. Genet. 26 (2025), 47–58, sections 3.1 and 3.2. <https://doi.org/10.1038/s41576-024-00772-4>
