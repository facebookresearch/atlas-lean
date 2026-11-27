# Extended cut edge transfer metric on semi-directed networks

**Setting.** Semi-directed binary phylogenetic networks on a leaf set $X$, level-1 networks and the cut edge transfer (CET) are as in the companion article; $r(N)$ is the number of reticulations. Two further moves change $r$ by one:

- **CET$^-$**: for a reticulation edge $e=(u,v)$ with $u$ not a reticulation (or $e$ a loop), delete $e$, undirect the other edge entering $v$, and suppress $u$ and $v$ (if $e$ is a loop, delete $u$).
- **CET$^+$**: the inverse operation: subdivide an edge by a new vertex $v$ and either attach a new vertex $u$ carrying a loop, or subdivide a second edge by $u$, add the arc $(u,v)$ and direct one other edge at $v$ into $v$.

An *extended CET* is any one of CET, CET$^+$, CET$^-$. A **CET$_1$** is a local CET in which the edge receiving the moved subnetwork is incident with one of the two edges that met the deleted cut edge at $u$; on trees it is an NNI move.

**Theorem.**

1. The space of all semi-directed level-1 networks on $X$, and the space of all semi-directed phylogenetic networks on $X$, are connected under extended CET.
2. Hence the minimum number of extended CETs transforming $N$ into $N'$ is a metric on each of these spaces.
3. If two semi-directed level-1 networks with exactly $k$ reticulations are one CET apart, and that CET neither moves a pair of parallel edges nor exchanges a loop for two parallel pairs, they are joined by a sequence of CET$_1$ moves through level-1 networks with $k$ reticulations (almost level-1 when $k=|X|-1$). Consequently, under CET$_1$ the space of semi-directed level-1 networks with exactly $k$ reticulations is connected if $k\le|X|-2$ and weakly connected if $k=|X|-1$.

## Depends on

- [Cut edge transfer connects tiers of level-1 networks](cet-connectedness-of-level-1-network-tiers.md)

## Expansion

Order the reticulations so that none is a descendant of a later one in a rooted partner, and remove them one by one with CET$^-$; the parent end of each removed edge is then never a reticulation, so every intermediate is a valid (level-1, if the start was) semi-directed network, and the process ends at an unrooted phylogenetic tree. Unrooted trees on $X$ are connected under SPR, which coincides with CET on trees, and running the same reduction backwards from the target network (each CET$^-$ is undone by a CET$^+$) completes the path. All three moves are reversible, so the induced path length is symmetric and satisfies the triangle inequality. For CET$_1$, a long-range CET is simulated by sliding the attachment point of the pruned subnetwork step by step along an undirected path to the recipient edge, checking that no step creates an extra $2$-cycle or loop. This supports local search heuristics (NNI-type moves on tree and reticulation edges) for semi-directed network inference.

## Sources

- Simone Linz and Kristina Wicke, "Exploring spaces of semi-directed level-1 networks", Journal of Mathematical Biology 87 (2023), 70, <https://doi.org/10.1007/s00285-023-02004-5>; numbering as in arXiv:2301.10818: Section 5.2 (Theorems 5.3 and 5.4, Corollary 5.5) and Section 5.3 (Proposition 5.6, Corollary 5.7).
