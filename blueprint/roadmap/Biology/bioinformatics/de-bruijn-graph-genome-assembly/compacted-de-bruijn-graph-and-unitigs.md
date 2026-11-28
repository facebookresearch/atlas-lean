# Compacted de Bruijn graph and unitigs

**De Bruijn graph of a $k$-mer set.** Let $K$ be a set of $k$-mers (strings of length $k$ over $\{A, C, G, T\}$). The node-centric de Bruijn graph $G(K)$ has vertex set $K$ and an edge $u \to v$ whenever the length-$(k-1)$ suffix of $u$ equals the length-$(k-1)$ prefix of $v$. In the bidirected version used for sequencing data, a $k$-mer and its reverse complement are identified.

**Unitigs.** A path $v_1 \to v_2 \to \dots \to v_\ell$ in $G(K)$ is *non-branching* if every internal step is forced: for $1 \le i < \ell$, $v_i$ has out-degree $1$ and $v_{i+1}$ has in-degree $1$. A *unitig* is a maximal non-branching path. Its string is the spelling $v_1 \cdot v_2[k] \cdot v_3[k] \cdots v_\ell[k]$, of length $k + \ell - 1$.

**Compacted de Bruijn graph.** Contracting every unitig to a single vertex labeled by its string gives the compacted de Bruijn graph: vertices are unitigs, and edges are the $(k-1)$-overlaps between unitig ends.

**Properties.**

1. The unitigs partition $K$: every $k$-mer lies in exactly one unitig (a cycle of in- and out-degree-$1$ vertices forms a single circular unitig).
2. Compaction preserves the graph's path structure: walks in $G(K)$ correspond one-to-one to walks in the compacted graph read at $k$-mer resolution, so the set of strings spelled by walks is unchanged.
3. The compacted graph has at most as many vertices as $G(K)$, typically far fewer, and is the standard intermediate representation in de Bruijn graph assembly.

BCALM 2 computes the compacted graph directly from the $k$-mers of a read set in low memory by distributing $k$-mers into buckets by minimizers, compacting within buckets in parallel, and gluing unitig fragments across buckets.

## Depends on

- [The k-mers of a string](kmers.md)
- [De Bruijn multigraph of a string](de-bruijn-edges.md)

## Expansion

Within a non-branching path the successor of each $k$-mer is unique, so no assembly decision is lost by merging it with its successor; any branching (a $k$-mer with two possible extensions or two predecessors) ends the unitig. Maximal non-branching paths are disjoint because a vertex with in- and out-degree $1$ lies on exactly one maximal such path, and branching vertices start or end paths. Property 2 follows because contraction only removes vertices whose single in-edge and single out-edge are merged into the label. The minimizer partition lets each bucket be processed independently: a $k$-mer can be compacted with a neighbor in the same bucket immediately, and unitig ends that straddle buckets are joined in a final gluing pass.

## Sources

- R. Chikhi, A. Limasset, P. Medvedev, "Compacting de Bruijn graphs from sequencing data quickly and in low memory", Bioinformatics 32(12) (2016) i201–i208, <https://doi.org/10.1093/bioinformatics/btw279> (PMC4908363).
- P. A. Pevzner, H. Tang, M. S. Waterman, "An Eulerian path approach to DNA fragment assembly", Proc. Natl. Acad. Sci. USA 98 (2001) 9748–9753.
