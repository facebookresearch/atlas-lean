# Ancestral haplotype reconstruction and Li–Stephens copying on a tree sequence

Let $H\in\{0,1\}^{n\times m}$ be phased haplotypes of $n$ samples at $m$ biallelic sites with known ancestral (0) and derived (1) states, assume each derived allele arose by a single mutation (infinite sites), and order sites by a proxy for allele age (by default the derived-allele frequency, older = more frequent). Tree-sequence inference proceeds in three steps.

1. **Ancestor for a focal site $\ell$.** Set $a_\ell=1$ and $a_k=-1$ (non-ancestral) elsewhere, and let $S$ be the set of samples carrying the derived allele at $\ell$. Scanning independently rightwards and leftwards from $\ell$: at a younger site set $a_k=0$; at an older site set $a_k$ to the majority allele among the samples in $S$, and evict from $S$ any sample that disagrees with this consensus at two consecutive older sites (disagreement is read as that sample having recombined out of the clade). Stop the scan once $|S|$ falls to at most half its initial size.
2. **Copying paths.** Process ancestors from oldest to youngest, then samples. Each haplotype is matched, by the Viterbi algorithm of the Li–Stephens haplotype-copying HMM, to a mosaic of strictly older ancestral haplotypes; every maximal copied segment $[l,r)$ from parent $p$ becomes an edge $(l,r,p,\text{child})$ of the tree sequence.
3. **Tree-sequence substrate.** The partially built tree sequence is itself used as the reference panel: Viterbi likelihoods are stored per node of the current marginal tree, a node whose likelihood equals its parent's is marked and not stored, and the compressed likelihoods are updated as the scan moves along the genome and the marginal tree changes.

Standard Li–Stephens Viterbi costs $O(nm)$ per haplotype for a panel of $n$ references; with roughly one ancestor per site ($n\approx m$) this is $O(m^2)$ per haplotype, which step 3 avoids because likelihoods cluster on subtrees and compress well. Under exact matching only five distinct likelihood values occur. As an empirical check, not a proof: when the true ancestral haplotypes of a simulated tree sequence (with mutations added to mark every ancestral segment endpoint) are supplied in place of step 1, the copying step reproduced the input tree sequence exactly in all tested cases.

## Remarks

Only the relative age order of nearby alleles matters for topology, which is why frequency is an adequate age proxy: misordered alleles far apart along the chromosome rarely have overlapping ancestral haplotypes. The eviction rule makes reconstructed ancestors deliberately long, since an over-long ancestor is repaired by later copying while a truncated one cannot be. Copying only from older haplotypes enforces a time order, so the resulting edges define a valid genealogy. The output is a tree sequence whose size grows far more slowly than the raw genotype matrix, and which can be used for downstream site and branch statistics.

## Depends on

- [The Li–Stephens copying model](../../../population-structure/li-stephens-haplotype-copying-model/hmm.md)

## Sources

- J. Kelleher, Y. Wong, A. W. Wohns et al., "Inferring whole-genome histories in large population datasets", Nat. Genet. 51 (2019), Online Methods ("Age of alleles", "Inferring ancestral haplotypes", "Copying process"), <https://doi.org/10.1038/s41588-019-0483-y>, PMCID PMC6726478.
