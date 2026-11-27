# Cut edge transfer connects tiers of level-1 networks

**Setting.** A *rooted binary phylogenetic network* on a leaf set $X$ is an acyclic digraph whose root has in-degree $0$ and out-degree $1$, whose leaves (out-degree $0$, in-degree $1$) are $X$, and whose other vertices are tree vertices (in/out-degree $1/2$) or reticulations ($2/1$); parallel edges are allowed. A *semi-directed* network is obtained from a rooted one (a *rooted partner*) by deleting the root, suppressing its child, and undirecting all tree edges. A rooted network is **level-1** if every cycle of its underlying graph has length at least $3$ and no two cycles share a vertex; a semi-directed network is level-1 if it has a level-1 rooted partner. Level-1 networks have at most $|X|-1$ reticulations. A network is *almost level-1* if it additionally may have one $2$-cycle (rooted case), respectively at most two $2$-cycles and no loop or at most one loop and no $2$-cycle (semi-directed case).

A **cut edge transfer (CET)** deletes a cut edge $e=\{u,v\}$ (where $u$ is not a reticulation and, in the semi-directed case, some rooted partner has $u$ as parent of $v$ or has $u,v$ as the two children of the root's child via cut edges), suppresses $u$, subdivides an edge of the component not containing $v$ by a new vertex $u'$, and adds the edge $\{u',v\}$ (directed $(u',v)$ in the rooted case). On trees, CET is rooted (respectively unrooted) subtree prune and regraft. A space is *connected* under CET if any two of its members are joined by a CET sequence staying in the space, and *weakly connected* if this holds with all intermediate networks almost level-1.

**Theorem.** Fix $k\ge0$.

1. If $k\le|X|-2$, the space of rooted level-1 networks on $X$ with exactly $k$ reticulations is connected under CET; if $k=|X|-1$ it is weakly connected. Any two such networks are joined by at most $10|X|+4k$ CETs, so the diameter is $O(|X|+k)$.
2. The same statements hold for semi-directed level-1 networks on $X$ with exactly $k$ reticulations.
3. Connectedness genuinely needs almost level-1 intermediates when $k=|X|-1$: for $|X|=2$, $k=1$, the two semi-directed level-1 networks that differ by swapping the leaves are not joined by any CET sequence within level-1 networks.

## Expansion

Every rooted level-1 network with $k$ reticulations is transformed, using at most $2|X|+2k$ CETs, into a network of *standard shape* (one that differs from a fixed canonical level-1 network with $k$ reticulations, the *standard form*, only by a permutation of leaf labels), and then by at most $3|X|$ further CETs into the standard form itself; reversibility of CET joins any two networks through the standard form. When $k=|X|-1$ there is no spare leaf to move cycles past one another, so one $2$-cycle is temporarily allowed. A CET between two (almost) level-1 rooted partners induces at most one CET between the corresponding semi-directed networks (a case analysis on whether the moved or the receiving edge touches the root's child), so rooted CET sequences project to semi-directed ones of no greater length. This settles connectivity of the search space used by level-1 network inference tools that operate on semi-directed networks with a fixed number of reticulations.

## Sources

- Simone Linz and Kristina Wicke, "Exploring spaces of semi-directed level-1 networks", Journal of Mathematical Biology 87 (2023), 70, <https://doi.org/10.1007/s00285-023-02004-5>; numbering as in arXiv:2301.10818: Section 3 (Lemmas 3.1–3.2, CET definition), Section 4 (Lemmas 4.3–4.4, Theorem 4.5), Section 5.1 (Theorem 5.1, Lemma 5.2).
