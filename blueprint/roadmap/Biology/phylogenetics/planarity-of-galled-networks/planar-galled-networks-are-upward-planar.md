# Planar galled networks are upward planar

**Setting.** A binary phylogenetic network $N$ on a leaf set $X$ is a rooted acyclic digraph with a root $\rho$ of in-degree $0$ and out-degree $1$, leaves of in-degree $1$ and out-degree $0$ bijectively labeled by $X$, tree vertices of in-degree $1$ and out-degree $2$, and reticulation vertices of in-degree $2$ and out-degree $1$; $\overline N$ denotes its underlying undirected graph. A *galled cycle* is a subgraph formed by two internally disjoint directed paths from a common tree vertex (its top) to a common reticulation $r$ in which every vertex other than $r$ is a tree vertex. $N$ is a *galled network* if every reticulation lies in a unique galled cycle. Planarity notions refer to $\overline N$: $N$ is *planar* if $\overline N$ has a planar drawing, *upward planar* if it has a planar drawing in which every arc is drawn monotonically upward, *terminal planar* if it has a planar drawing with $\rho$ and all leaves on the outer face, and *outerplanar* if it has a planar drawing with every vertex on the outer face.

**Statement.** A galled network is planar if and only if it is upward planar.

More precisely, for a planar drawing $\Gamma$ of any binary phylogenetic network $N$, there is an upward planar drawing strongly equivalent to $\Gamma$ (same faces and same incidences, outer face preserved) if and only if $\Gamma(\rho)$ lies on the outer face and every cycle $C$ of $N$ contains a reticulation $r$ with parents $p_1,p_2$ and child $v$ such that $\Gamma(p_1),\Gamma(p_2)$ lie on the Jordan curve $\Gamma(C)$ while the arc $(r,v)$ is drawn in the exterior of $C$.

For general phylogenetic networks outerplanar $\subsetneq$ terminal planar $\subsetneq$ upward planar $\subsetneq$ planar, so the statement says that the last inclusion is an equality on galled networks.

## Expansion

In a galled network every reticulation $r$ with child $v$ is a cut vertex of $\overline N$ and $\{r,v\}$ is a cut edge. Start from a planar drawing with the root on the outer face. If the child edge of some reticulation points into the interior of its galled cycle (an inward galled cycle), the part of the network hanging below that cut edge is a 1-bridge of the cycle attached only at $r$, so it can be moved into the face on the other side of $r$ without creating crossings. Each move reduces the number of inward galled cycles, and once none remain the Thomassen-type criterion above applies: every cycle contains a reticulation whose child edge leaves the cycle outward, which is exactly the condition for an upward drawing equivalent to the planar one.

## Sources

- Hexuan Liu, Taoyang Wu, Guan-Ru Yu, "Characterisations of Planar Galled Networks", arXiv:2609.28597 (2026), Theorem 2 and Theorem 3, <https://doi.org/10.48550/arXiv.2609.28597>
