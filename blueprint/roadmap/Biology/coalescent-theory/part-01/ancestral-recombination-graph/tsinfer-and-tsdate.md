# Tree-sequence dating (tsdate)

The inference of a tree sequence from phased biallelic genotypes by ancestral haplotype reconstruction and Li–Stephens copying from older ancestors (tsinfer) is stated in [ancestral haplotype reconstruction and Li–Stephens copying on a tree sequence](../../two-locus-coalescent/tree-sequence-inference-by-ancestral-haplotype-copying/ancestral-haplotype-reconstruction-and-li-stephens-copying.md); its output is a single topology. tsdate (Wohns et al. 2022) assigns ages to the nodes of any valid tree sequence by a Bayesian method; as summarized by Nielsen, Vaughn and Deng (2025, section 3.2), it estimates branch lengths from the distribution of mutations on branches under a coalescent prior. Dating does not estimate a posterior over topologies: the review classes tsinfer with methods that infer a single topology.

## Expansion

1. The dating model: a coalescent prior on node times, a Poisson likelihood for the mutation counts on edges, and the constraint that parents are older than children; the approximate posterior computation.
2. What the output does not establish: recovery of the true ancestral recombination graph or calibrated uncertainty for its topology.

## Sources

- A. W. Wohns et al., A unified genealogy of modern and ancient genomes, Science 375 (2022), eabi8264, Results and Fig. 1. <https://doi.org/10.1126/science.abi8264>
- R. Nielsen, A. H. Vaughn and Y. Deng, Inference and applications of ancestral recombination graphs, Nat. Rev. Genet. 26 (2025), 47–58, sections 3.1 and 3.2. <https://doi.org/10.1038/s41576-024-00772-4>
