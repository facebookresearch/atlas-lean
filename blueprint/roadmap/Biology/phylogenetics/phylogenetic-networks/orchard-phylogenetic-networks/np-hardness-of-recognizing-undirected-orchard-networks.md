# NP-hardness of recognizing undirected orchard networks

**Definitions.** In a rooted binary phylogenetic network a *cherry* is an ordered pair of leaves $(x,y)$ with a common parent, and a *reticulated cherry* is a pair $(x,y)$ in which the parent $p$ of $x$ is a reticulation and $p$ and $y$ have a common parent. *Reducing* by a cherry deletes $x$; reducing by a reticulated cherry deletes the arc from $y$'s parent to $x$'s parent; degree-$2$ vertices are then suppressed. A network is an *orchard* if some sequence of such reductions brings it down to a single arc (rooted case) or a single vertex (undirected case, with the analogous undirected reductions). Orchards model tree-like evolution with horizontal gene transfer. An *orientation* of an undirected network subdivides one edge, attaches a root there and directs all edges; an *orchard orientation* is an orientation that is a rooted orchard.

**Theorem.**

1. An undirected binary network is an orchard if and only if it has an orchard orientation.
2. **Orchard Recognition** (is a given undirected binary network an orchard?) and **Orchard Orientation** (does it have an orchard orientation?) are NP-hard.

By contrast, recognizing whether a *directed* network is an orchard takes polynomial time, since cherries and reticulated cherries can be reduced greedily in any order.

## Expansion

The equivalence (1) shows that undirected reduction sequences correspond to rooted ones for a suitable root placement, so the difficulty of the undirected problem lies in choosing where to root. Hardness is by reduction from 3-SAT: a fixed subnetwork (the "sheep") can only be oriented as an orchard if the root lies inside it, so any successful reduction sequence must chase through the network and end in the sheep. Choice widgets encode truth assignments, wire, and-, replicator and clause widgets propagate them, and a formula is satisfiable if and only if the assembled network is an orchard. A rooted orchard is equivalently a network admitting a horizontal-gene-transfer-consistent labelling, i.e. it can be drawn as a base tree with horizontal arcs.

## Sources

- Jordan Dempsey, Leo van Iersel, Mark Jones, Yukihiro Murakami and Norbert Zeh, "A wild sheep chase through an orchard", Journal of Computer and System Sciences 165 (2027), 103879, <https://doi.org/10.1016/j.jcss.2026.103879>; numbering as in arXiv:2408.10769: Section 2 (reductions, orientations, Theorem 2.1), Theorem 3.1 and Section 4 (widgets, Theorem 4.18).
