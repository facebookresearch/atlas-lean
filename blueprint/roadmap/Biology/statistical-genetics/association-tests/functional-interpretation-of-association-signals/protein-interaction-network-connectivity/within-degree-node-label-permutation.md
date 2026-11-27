# Within-degree node-label permutation null for interaction networks

Let $G = (V, E)$ be a reference graph of high-confidence protein–protein interactions, with degree $d(v)$ for $v \in V$. Let $\mathcal{L}_1, \dots, \mathcal{L}_m$ be disjoint sets of proteins, one per associated genomic locus, and let a network statistic $T$ be a function of the induced subgraph structure (for instance the number of edges of $G$ joining proteins of two different loci).

A **within-degree node-label permutation** is a bijection $\sigma: V \to V$ satisfying $d(\sigma(v)) = d(v)$ for all $v$, drawn uniformly from the permutations with that property; the graph is kept fixed and only the labels move. The null distribution of $T$ is its distribution under $T(\sigma(\mathcal{L}_1), \dots, \sigma(\mathcal{L}_m))$ over many such $\sigma$, and the $p$-value is the proportion of permutations reaching the observed value.

The construction holds fixed, exactly, three features of the data that would otherwise generate false signal: the graph's size, its edge count, and the degree of each protein. A protein that binds promiscuously in vitro, or one that has been studied so often that many of its interactions are recorded, keeps its degree under $\sigma$ and so contributes the same expected connectivity in the null as in the data. What the permutation does not preserve is which high-degree proteins sit in the associated loci, which is exactly the hypothesis under test.

Two alternative nulls are weaker. Sampling random SNPs matched for gene content and binding degree fails when some loci have extreme gene density or extreme degree, because no matched sample exists. Permuting edges destroys the local structure of the reference graph, so the null graph is no longer the biological one.

## Expansion

Degree-preserving label permutation is the configuration-model idea applied to labels rather than edges: it defines a null in which the only thing randomized is the correspondence between biology (which proteins the loci contain) and topology (where the hubs are). Conditioning on the degree sequence matters because connectivity statistics in a graph with a heavy-tailed degree distribution are dominated by hubs — the expected number of edges between two random sets of sizes $k_1, k_2$ grows with the product of their degree sums — so an unconditioned null would call any hub-containing locus set significant. Restricting to exact degree equality is feasible because degrees are integers with many ties; proteins are bucketed by degree and labels are shuffled within buckets, with near-degree bucketing when a degree class is a singleton. Applied with 50,000 permutations to loci from rheumatoid arthritis and Crohn's disease, the observed number of inter-locus edges was significant ($p$ of order $10^{-3}$ or smaller), and the same test on a Mendelian positive control reproduced its known complex.

## Sources

- E. J. Rossin, K. Lage, S. Raychaudhuri et al., "Proteins encoded in genomic regions associated with immune-mediated disease physically interact and suggest underlying biology", PLoS Genetics 7 (2011), e1001273, Results ("A method to assess network connectivity", Figs. 1–2) and Text S1, <https://doi.org/10.1371/journal.pgen.1001273>, PMCID PMC3020935.
