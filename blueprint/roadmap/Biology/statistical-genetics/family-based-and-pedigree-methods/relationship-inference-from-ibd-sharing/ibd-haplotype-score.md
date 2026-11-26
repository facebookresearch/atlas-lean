# IBD haplotype score

Let individuals $i$ and $j$ share a set $S$ of identity-by-descent (IBD) segments, inferred from phased genotypes, with IBD2 regions masked. For a segment $s$ let $l_s$ be its genetic length and $i_s \in \{0,1\}$ the index of the haplotype of $i$ on which it lies, and let $S_c \subseteq S$ be the segments on chromosome $c$.

**Definition.** The haplotype score of $i$ in the pair $(i,j)$ is

$$h_i(ij) = \frac{\sum_{c} \max\Bigl\{\sum_{s \in S_c} l_s\, \mathbf 1(i_s = 0),\ \sum_{s \in S_c} l_s\, \mathbf 1(i_s = 1)\Bigr\}}{\sum_{s \in S} l_s} \in \Bigl[\tfrac12, 1\Bigr],$$

the length-weighted, per-chromosome fraction of shared IBD that lies on a single haplotype of $i$. The per-chromosome maximum is needed because haplotype labels are not coordinated across chromosomes.

**Separation of second-degree relationships.** With error-free phasing:

- half-siblings are related through a single parent of each, so all IBD lies on one haplotype of each: $h_i(ij) = h_j(ij) = 1$;
- in a grandparent–grandchild or avuncular pair, the younger relative (grandchild, niece or nephew) shares IBD through one parent only, so its score is $1$, while the older relative (grandparent, aunt or uncle) shares IBD on both of its haplotypes, so its score is below $1$.

The pair $(h_i(ij), h_j(ij))$ therefore distinguishes half-siblings from the other second-degree relationships, which have the same expected IBD1 and IBD2 proportions, and orients the generations within a pair.

## Expansion

All second-degree relatives share on average a quarter of their genome IBD1 and nothing IBD2, so the proportions $(\hat\pi_1, \hat\pi_2)$ fix the degree but not the type of the relationship. The haplotype score uses the parental origin of the shared segments instead. Long-range phasing switch errors scramble haplotype indices along a chromosome and pull both scores toward $\tfrac12$. The source trains its classifier on scores computed after simulated switch errors (exponential inter-error distances with mean $25$ cM) and adds a "phase error" class that suppresses the inference when scores are uninformative. In an endogamous sample of 700 Himba individuals, seeding with high-confidence first-degree pairs and then classifying by IBD summaries and haplotype scores recovered first- through fourth-degree relationships.

## Sources

- C. M. Williams, B. A. Scelza, S. D. Slack, et al., "A rapid accurate approach to inferring pedigrees in endogamous populations", *Genetics* (2025), <https://doi.org/10.1093/genetics/iyaf094> (PMC12341879; Equations (1) and (2), section "Haplotype score classifier").
