# ARG total variation distance

An ARG on a set of sampled genomes assigns to each genomic position $s$ a marginal tree. Every branch of that tree subtends a set $S$ of sampled genomes, and a mutation placed on the branch is carried exactly by $S$. Sampling a mutation uniformly over the total branch length (area) of the ARG therefore induces a probability distribution $P_{\mathcal G}$ on pairs $(s, S)$, with mass at $(s, S)$ proportional to the total length of branches at $s$ subtending exactly $S$. For two ARGs $\mathcal G, \mathcal G'$ on the same samples and sequence, the **ARG total variation distance** is

$$d_{\mathrm{TV}}(\mathcal G, \mathcal G') = \sup_{A}\bigl|P_{\mathcal G}(A) - P_{\mathcal G'}(A)\bigr| = \tfrac12\sum_{(s,S)}\bigl|P_{\mathcal G}(s,S) - P_{\mathcal G'}(s,S)\bigr|,$$

the second form holding with the sum read as an integral over positions. It lies in $[0,1]$, equals $0$ when the two ARGs generate the same mutation distribution, and equals $1$ when they share no mutation pattern. Unlike the Robinson–Foulds distance, which counts the bipartitions present in one tree but not the other, it weights each predicted mutation pattern by its branch length, so it measures accuracy in predicting unobserved variants. Polytomies need no random resolution: they simply concentrate mass on fewer carrier sets.

## Depends on

- [Genome ARGs: interval-annotated inheritance graphs and their local trees](../genome-arg-interval-annotated-inheritance-graph.md)

## Expansion

The carrier set of a mutation determines its genotype vector, so two ARGs that place equal branch length on every carrier set at every position predict the same distribution of new variants. Topological agreement on a short branch counts little and agreement on a long branch counts a lot, matching how much each branch contributes to observable variation. This makes the metric suited to judging ARGs inferred for downstream association and imputation, where the question is which unobserved variants, carried by which samples, the genealogy implies. Variants of the metric normalize branch lengths or stratify mutations by allele frequency.

## Sources

- B. C. Zhang, A. Biddanda, Á. F. Gunnarsson, F. Cooper, P. F. Palamara, "Biobank-scale inference of ancestral recombination graphs enables genealogical analysis of complex traits", Nature Genetics 55 (2023), Methods (ARG total variation distance) and Supplementary Note 2, <https://doi.org/10.1038/s41588-023-01379-x> (PMC10181934).
