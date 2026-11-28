# XBWT run bound for reads grafted onto an assembled genome

**Setting.** Let $G$ be a string over a finite alphabet (an assembled genome) and let a readset consist of substrings of $G$ together with their alignment positions. Build an edge-labelled tree $T$ by taking the path spelling $G$ as a trunk and grafting (appending) each read as a path that starts at the trunk node of its aligned position, so that, for reads that match $G$ exactly, all edges at the same depth carry the same label. The eXtended Burrows–Wheeler Transform (XBWT) of a labelled tree lists, for the nodes sorted co-lexicographically by their upward path labels, the labels of their outgoing edges; a *run* is a maximal block of equal consecutive symbols.

**Theorem (exact reads).** If every grafted read equals the substring of $G$ at its aligned position, then the XBWT of $T$ has exactly as many runs as the BWT of the reverse of $G$.

**Theorem (reads with errors).** Suppose grafted reads may differ from $G$ by insertions, deletions or substitutions, and let $\delta$ be the average distance from a read's *first* difference to its *end*. Then the XBWT of $T$ has at most $2\delta$ additional runs per read compared with the exact case.

**Corollary (compressed index).** Let $T$ have $n$ vertices, let $r$ be the number of runs in its XBWT and $t$ the number of reads. Then $T$ can be stored in $O(r + t)$ words so that, given a pattern $P$, all $k$ vertices reachable by paths labelled $P$ are reported in $O\big((|P| + k)\log\log n\big)$ time.

## Expansion

Exact reads introduce no new contexts: a node of a grafted read and the trunk node at the same depth have the same upward label up to the graft point, so they sort next to each other and carry the same outgoing label, adding no run boundary. After a read's first difference its nodes get contexts not on the trunk, and each of the at most $\delta$ such nodes on average can split a run in two places. The corollary follows from a more general result for Wheeler graphs decomposable into $\upsilon$ edge-disjoint unary paths ($O(r + \upsilon)$ space, $O(|P| \log\log|G|)$ counting, $O(\log\log|G|)$ per reported vertex), applied with one path per read. In contrast, the Extended BWT indexes each read as a separate string and pays per-string overhead.

## Depends on

- [Burrows–Wheeler transform](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/bwt.md)

## Sources

- T. Gagie, G. Gourdel and G. Manzini, "Compressing and Indexing Aligned Readsets", arXiv:1809.07320 (2018), Section 3 ("Our contribution"): the run-count theorems for exact and erroneous grafted reads, the Wheeler-graph locating theorem and its corollary, <https://doi.org/10.48550/arXiv.1809.07320>.
- Published version: T. Gagie, G. Gourdel and G. Manzini, "Compressing and Indexing Aligned Readsets", 21st International Workshop on Algorithms in Bioinformatics (WABI 2021), LIPIcs 201, Paper 13, <https://doi.org/10.4230/LIPIcs.WABI.2021.13>.
