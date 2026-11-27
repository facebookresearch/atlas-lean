# Within-degree node-label permutation null for interaction networks

Let $\mathcal{L}_1, \dots, \mathcal{L}_m$ be disjoint sets of proteins, one per associated genomic locus, and let $G = (V, E)$ be a reference graph of high-confidence protein–protein interactions from which every within-locus edge (an edge joining two proteins of the same $\mathcal{L}_r$) has been removed, with degree $d(v)$ for $v \in V$. Let a network statistic $T_H(\mathcal{L}_1, \dots, \mathcal{L}_m)$ be a function of the loci and a graph $H$ on $V$ (for instance the number of edges of $H$ joining proteins of two different loci).

A **within-degree node-label permutation** is a bijection $\sigma: V \to V$ satisfying $d(\sigma(v)) = d(v)$ for all $v$, drawn uniformly from the permutations with that property; it swaps vertices within each degree class and fixes every vertex whose degree no other vertex shares. A random network $G^*$ of the null is built in two steps:

1. **Permutation step.** Draw such a $\sigma$ and relabel $G$ by it, $G^\sigma = (V, \{\sigma(u)\sigma(v) : uv \in E\})$.
2. **Edge step.** Let $G_{\mathrm{unique}}$ be the union of the subnetworks consisting of the unique-degree vertices and their edges. Randomize $G_{\mathrm{unique}}$ inside $G^\sigma$ by degree-preserving edge switching: repeatedly select a pair of its edges $A$–$B$, $C$–$D$ at random and exchange their ends, giving $A$–$D$, $C$–$B$.

The null distribution of $T$ is the distribution of $T_{G^*}(\mathcal{L}_1, \dots, \mathcal{L}_m)$ over many such $G^*$, and the $p$-value is the proportion of random networks reaching the observed value $T_G(\mathcal{L}_1, \dots, \mathcal{L}_m)$.

Both steps hold fixed, exactly, three features of the data that would otherwise generate false signal: the graph's size, its edge count, and the degree of each protein. A protein that binds promiscuously in vitro, or one that has been studied so often that many of its interactions are recorded, keeps its degree in every random network and so contributes the same expected connectivity in the null as in the data. The edge step is needed because the permutation step cannot move a vertex of unique degree.

Two alternative nulls are weaker. Sampling random SNPs matched for gene content and binding degree fails when some loci have extreme gene density or extreme degree, because no matched sample exists. Permuting the edges of the whole graph destroys the local structure of the reference graph, so the null graph is no longer the biological one; the construction above confines edge switching to $G_{\mathrm{unique}}$, where the permutation step cannot act.

## Expansion

Degree-preserving label permutation is the configuration-model idea applied to labels rather than edges: it defines a null in which the only thing randomized is the correspondence between biology (which proteins the loci contain) and topology (where the hubs are). Conditioning on the degree sequence matters because connectivity statistics in a graph with a heavy-tailed degree distribution are dominated by hubs — the expected number of edges between two random sets of sizes $k_1, k_2$ grows with the product of their degree sums — so an unconditioned null would call any hub-containing locus set significant. Restricting to exact degree equality is feasible because degrees are integers with many ties; proteins are bucketed by degree and labels are shuffled within buckets, and the proteins of singleton degree classes, which no shuffle moves, are randomized by the edge switching on $G_{\mathrm{unique}}$. Applied with 50,000 permutations to loci from rheumatoid arthritis and Crohn's disease, the observed number of inter-locus edges was significant ($p$ of order $10^{-3}$ or smaller), and the same test on a Mendelian positive control reproduced its known complex.

## Sources

- E. J. Rossin, K. Lage, S. Raychaudhuri et al., "Proteins encoded in genomic regions associated with immune-mediated disease physically interact and suggest underlying biology", PLoS Genetics 7 (2011), e1001273, Results ("A method to assess network connectivity", Figs. 1–2) and Text S1, <https://doi.org/10.1371/journal.pgen.1001273>, PMCID PMC3020935.
