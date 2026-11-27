# Cherry-picking characterization of the unrooted hybrid number

**Setting.** An *unrooted phylogenetic network* on a leaf set $X$ is a simple connected graph $\mathcal{N} = (V, E)$ whose leaves are labeled by $X$ and whose internal vertices have degree three; its *reticulation number* is $r(\mathcal{N}) = |E| - (|V| - 1)$, the number of independent cycles. $\mathcal{N}$ *displays* an unrooted phylogenetic forest $\mathcal{F}$ on $X$ if $\mathcal{F}$ can be obtained from a subgraph of $\mathcal{N}$ by suppressing degree-two vertices. The *unrooted hybrid number* of two forests $\mathcal{F}, \mathcal{F}'$ on $X$ is

$$h(\mathcal{F}, \mathcal{F}') = \min\{r(\mathcal{N}) : \mathcal{N} \text{ displays } \mathcal{F} \text{ and } \mathcal{F}'\}.$$

A *cherry picking sequence* for $\mathcal{F}, \mathcal{F}'$ is a sequence $\sigma = (x_1, \dots, x_m)$ of leaves, $m \ge |X|$, with forests $\mathcal{F}[i], \mathcal{F}'[i]$ such that $\mathcal{F}[1] = \mathcal{F}$, $\mathcal{F}'[1] = \mathcal{F}'$, $\mathcal{F}[m] = \mathcal{F}'[m] = \{x_m\}$, and each step either (C1) deletes $x_i$ when $(x_i, y)$ is a cherry of both forests, (C3) deletes $x_i$ when it is an isolated vertex of one forest, or (C2) when $(x_i, y)$ is a cherry of one forest but not of the other, cuts one prescribed edge near $x_i$ or $y$ in one of the forests (the admissible cuts depend on how $x_i$ and $y$ sit in the other forest) without deleting a leaf. Its *weight* is $w(\sigma) = m - |X|$, the number of cutting steps.

**Theorem.**

1. *(Existence.)* Every pair of forests on $X$ has a cherry picking sequence.
2. *(Characterization.)* For forests $\mathcal{F}, \mathcal{F}'$ on $X$,

    $$h(\mathcal{F}, \mathcal{F}') = \min\{w(\sigma) : \sigma \text{ a cherry picking sequence for } \mathcal{F}, \mathcal{F}'\}.$$

    More precisely, every cherry picking sequence yields a network displaying both forests with $r(\mathcal{N}) \le w(\sigma)$, and every such network yields a sequence with $w(\sigma) \le r(\mathcal{N})$.

3. *(TBR distance.)* For two unrooted phylogenetic trees $\mathcal{T}, \mathcal{T}'$ on $X$, the tree bisection and reconnection distance satisfies

    $$d_{\mathrm{TBR}}(\mathcal{T}, \mathcal{T}') = \min\{w(\sigma) : \sigma \text{ a cherry picking sequence for } \mathcal{T}, \mathcal{T}'\},$$

    recovering, with item 2, the known equality $h = d_{\mathrm{TBR}}$ for pairs of trees.

## Depends on

- [Tbr Dist](../../../not-yet-classified/tbragreement-forest/tbr-dist.md)

## Expansion

Cherry picking sequences were introduced for rooted networks, where picking a cherry corresponds to removing a leaf below a reticulation. In the unrooted setting there is no direction, so the sequence must also record edge cuts whenever the two forests disagree locally; each cut corresponds to one extra cycle in a network displaying both forests, and when both forests share a cherry the leaf can be removed for free. Building the network backwards from the sequence gives the upper bound, and peeling leaves off an optimal network gives the lower bound. The characterization turns the NP-hard hybrid number into a shortest-sequence problem amenable to search and kernelization arguments.

## Sources

- Katharina T. Huber, Simone Linz and Vincent Moulton, "Cherry picking in forests: A new characterization for the unrooted hybrid number of two phylogenetic trees", Discrete Mathematics & Theoretical Computer Science 27:2 (2025), 11633, <https://doi.org/10.46298/dmtcs.11633>; numbering as in arXiv:2212.08145: Section 3 (definition of cherry picking sequences), Proposition 3.2, Theorems 4.1, 4.2, 4.5 and 6.1.
