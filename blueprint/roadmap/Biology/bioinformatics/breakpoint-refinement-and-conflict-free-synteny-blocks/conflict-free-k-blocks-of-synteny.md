# Conflict-free k-blocks of synteny

**Anchors.** Given two genomes $G_r$ and $G_o$, an *anchor* is a pair of orthologous, non-overlapping markers, one in each genome, each marker in exactly one anchor. An anchor $a$ is described by its chromosomes, its ranks $a_r$, $a_o$ among markers on those chromosomes, and a relative orientation $\sigma_a \in \{+1,-1\}$. For anchors $a, b$ on the same chromosome pair,

$$d(a,b) = \max\bigl(|b_r - a_r|,\, |b_o - a_o|\bigr),$$

and $d(a,b) = \infty$ otherwise.

**Chaining graph.** For an integer $k \ge 1$ let $G_k$ be the directed graph on anchors with an arc $ab$ whenever $a_r < b_r$, $d(a,b) \le k$, and either $a_o < b_o$ with both orientations positive, or $a_o > b_o$ with both orientations negative.

**Conflicts.**
- Type I: arcs $ab$ and $cd$ in the same connected component of $G_k$ conflict if the markers of $a,b,c,d$ do not appear in the same order in both genomes.
- Type II: an arc $ab$ in component $C$ conflicts if some anchor $x$ whose marker lies between those of $a$ and $b$ in one genome belongs to a different component with at least $k$ vertices.

Let $H_k$ be the subgraph of $G_k$ keeping only non-conflicting arcs. A *$k$-block* is a connected component of $H_k$ with more than $k$ vertices; its extreme genomic coordinates define a synteny block.

**Properties.**
1. Synteny blocks from distinct $k$-blocks never intersect, in either genome (no type II conflicts).
2. Within a $k$-block the markers are totally ordered consistently in both genomes (no type I conflicts), so each end of a block is a single anchor and the block ends are orthologous.
3. With $n$ anchors and fixed $k$, the $k$-blocks are computed in $O(nk^2 + n\log n)$ time: sorting gives the ranks, $G_k$ has at most $kn$ arcs, and each arc is checked for conflicts against at most $k$ other arcs or vertices.

## Expansion

A single parameter $k$ serves both as the maximal gap for chaining (number of intervening out-of-order markers) and as the minimal block size; using the same value prevents a block from lying inside another and prevents an irrelevant small block from breaking a large one. Instead of resolving conflicts, an NP-hard problem in some formulations, conflicting arcs are discarded, which may shorten blocks; the shortened ends are recovered by the subsequent alignment-based refinement of the region between consecutive blocks. Non-overlap and orthologous extremities are exactly what that refinement requires, since it aligns the sequence between two consecutive blocks with the sequences flanking their orthologues.

## Sources

- C. Lemaitre, E. Tannier, C. Gautier, M.-F. Sagot, "Precise detection of rearrangement breakpoints in mammalian chromosomes", BMC Bioinformatics (2008), Methods: building the synteny blocks (description, conflicts of types I and II, Figs. 2–3, complexity), <https://doi.org/10.1186/1471-2105-9-286>, PMCID PMC2443379.
