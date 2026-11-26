# Read-depth multiplicity of assembly-graph contigs

**Setting.** A haploid genome consisting of replicons present once per cell is sequenced with reads placed uniformly at random, at expected per-base depth $D$. In the assembly graph, a contig $x$ whose sequence occurs $k_x \ge 1$ times in the genome collapses those copies, and every read from any copy maps to it. Let $d_x$ be the median read depth along $x$.

**Proposition.** Under uniform read placement the expected depth of each base of $x$ is $k_x D$. Hence $\hat k_x = \operatorname{round}(d_x / \hat D)$, with $\hat D$ the median depth per base over the whole assembly, is a consistent estimate of the multiplicity as coverage grows: single-copy contigs have $d_x \approx \hat D$ and repeat contigs $d_x \approx k_x \hat D$.

**Caveat (copy number).** If a replicon is present at $n$ copies per cell, all its contigs have depth near $n k_x D$, so depth alone identifies only the product $n k_x$; a contig of depth $2D$ may be a two-copy chromosomal repeat or a single-copy contig on a two-copy plasmid.

## Depends on

- [Depth of coverage of a base](../lander-waterman-coverage-model/depth.md)

## Expansion

Each copy of the sequence independently attracts reads at rate $D$ per base, and collapsing $k_x$ copies sums their coverage, giving $k_x D$ by linearity of expectation. To resolve the copy-number ambiguity the source combines depth with graph structure: repeat contigs usually have several connections at each end, single-copy contigs at most one. It seeds multiplicity $1$ on contigs near the median depth with at most one connection per end, then propagates multiplicities greedily wherever depth and connections agree. The resulting single-copy contigs are the anchors that paired-end and long-read bridges connect.

## Sources

- R. R. Wick, L. M. Judd, C. L. Gorrie and K. E. Holt, *Unicycler: Resolving bacterial genome assemblies from short and long sequencing reads*, PLoS Comput. Biol. 13 (2017), e1005595. <https://doi.org/10.1371/journal.pcbi.1005595> (PMCID: PMC5481147). Design and implementation, "Multiplicity".
- E. S. Lander and M. S. Waterman, *Genomic mapping by fingerprinting random clones: a mathematical analysis*, Genomics 2 (1988), 231–239. <https://doi.org/10.1016/0888-7543(88)90007-9>
