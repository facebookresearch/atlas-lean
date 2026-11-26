# Normal networks are determined by shortest inter-taxa distances

Let $(\mathcal{N}, w)$ be a rooted phylogenetic network on a leaf set $X$ with edge weights $w$. An *up-down path* between leaves $x$ and $y$ climbs from $x$ to a vertex and then descends to $y$. The *minimum distance matrix* $\mathcal{D}_{\min}$ has $(x,y)$-entry $d_{\min}(x,y)$, the minimum length of an up-down path joining $x$ and $y$. A weighting is *equidistant* if all root-to-leaf paths have the same length, and a *reticulation-pair weighting* if the two edges into each reticulation have equal weight. A network is *normal* if it is tree-child (every non-leaf vertex has a non-reticulation child) and has no shortcuts. Two weighted networks are *equivalent* if they differ only by re-weighting the edges at reticulations without changing the sums of weights through each reticulation.

**Theorem.**

1. If $(\mathcal{N}, w)$ is an equidistant-weighted normal network on $X$, it is, up to equivalence, the unique such network realizing $\mathcal{D}_{\min}$, and a member of its equivalence class can be computed from $\mathcal{D}_{\min}$ in $O(|X|^3)$ time.
2. If $(\mathcal{N}, w)$ is a reticulation-pair weighted normal network on $X \cup \{r\}$ with outgroup $r$, it is, up to equivalence, the unique such network realizing $\mathcal{D}_{\min}$ on $X$ together with the maximum distance outgroup vector (for each $x$, the maximum length of an up-down path from $x$ to $r$), and a representative can be computed in $O(|X|^3)$ time.

Both statements extend to temporal tree-child networks, which have no shortcuts, but not to general tree-child networks, where shortest distances cannot detect shortcuts.

## Expansion

The algorithm repeatedly takes a pair $\{s,t\}$ minimizing $d_{\min}$. In an equidistant normal network such a pair is a cherry or a reticulated cherry, and which case holds, and which leaf is the reticulation leaf, is read off from the distances to the other taxa ($d_{\min}(s,x) = d_{\min}(t,x)$ for all other $x$ signals a cherry). Reducing the cherry or cutting the reticulated cherry gives a smaller normal network whose minimum distance matrix is computed from the current one, so induction reconstructs the network. Earlier results needed the full set or multiset of all up-down path lengths, of which there can be exponentially many; the theorem shows that only the shortest ones are needed for normal networks.

## Sources

- Magnus Bordewich, Katharina T. Huber, Vincent Moulton and Charles Semple, *Recovering tree-child networks from shortest inter-taxa distance information*, arXiv:1711.08866, Theorems 2.3 and 2.4 (Section 2), proved in Sections 4 and 5. <https://doi.org/10.48550/arXiv.1711.08866> Published version: Journal of Mathematical Biology 77 (2018) 571–594, <https://doi.org/10.1007/s00285-018-1218-x>.
