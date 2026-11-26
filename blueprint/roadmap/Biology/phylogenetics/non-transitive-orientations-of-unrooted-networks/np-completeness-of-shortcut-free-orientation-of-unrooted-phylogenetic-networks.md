# NP-completeness of shortcut-free orientation of unrooted phylogenetic networks

**Setting.** An *unrooted binary phylogenetic network* $U$ on a finite set $L$ is a simple connected graph whose vertices have degree $1$ or $3$, with the degree-$1$ vertices bijectively labeled by $L$. A *rooted binary phylogenetic network* on $L$ is a simple acyclic digraph with a unique root of in-degree $0$ and out-degree $2$, leaves of in-degree $1$ and out-degree $0$ bijectively labeled by $L$, and all other vertices of in/out-degree $1/2$ or $2/1$. A rooted network $N$ is an *orientation* of $U$ if $N$ is obtained from $U$ by subdividing one edge with the root and directing every edge. An arc $(u,v)$ of $N$ is a *shortcut* (transitive arc) if there is another directed path from $u$ to $v$.

**Statement.** The problem Phylogenetic NT-Orientation, which asks whether an unrooted binary phylogenetic network $U$ admits an orientation as a rooted binary phylogenetic network without shortcuts, is NP-complete. Hardness holds already for networks with a single leaf.

## Depends on

- [NP-completeness of non-transitive st-orientation of cubic graphs](np-completeness-of-non-transitive-st-orientation-of-cubic-graphs.md)

## Expansion

A candidate orientation is verified in polynomial time: the root is the unique source, the leaves are exactly the sinks, the digraph is acyclic, and no arc is bypassed. For hardness, start from an instance of NT-st-Orientation in which $s,t$ have degree $1$ and all other vertices have degree $3$. Replace the neighbourhood of $s$ by a *root gadget*, a modification of the fork gadget, and use $t$ as the unique leaf. In every non-transitive orientation of the resulting unrooted network the root subdivides an edge inside the gadget, away from the old neighbour of $s$, so restricting the orientation to the original edges gives a non-transitive $st$-orientation; conversely, a non-transitive $st$-orientation extends through the gadget. Shortcuts matter in phylogenetics because shortcut-free networks in which every non-leaf vertex has a tree child are exactly the normal networks.

## Sources

- Janosch Döcker, Simone Linz, "Orientations without transitive arcs for cubic graphs and phylogenetic networks", arXiv:2608.28654 (2026), Theorem 5.2, <https://doi.org/10.48550/arXiv.2608.28654>
