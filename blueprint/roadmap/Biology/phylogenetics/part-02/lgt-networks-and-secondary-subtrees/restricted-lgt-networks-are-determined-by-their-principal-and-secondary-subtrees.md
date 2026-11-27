# Restricted LGT networks are determined by their principal and secondary subtrees

**LGT networks.** An LGT network on a label set $S$ is a rooted phylogenetic network $N = (V,E)$ on $S$ with a partition $E = E_p \sqcup E_s$ such that $T_0(N) = (V, E_p)$ is a rooted tree with leaves labelled by $S$, the *principal subtree*. Arcs in $E_p$ are *principal* and arcs in $E_s$ *secondary*; each reticulation has exactly one principal incoming arc. A node is *principally elementary* if it has exactly one principal child. For a secondary arc $e = (u,h)$, the *secondary subtree* $T_e(N)$ is obtained from $T_0(N)$ by deleting the principal arc into $h$ and adding $e$. Write $\tilde T$ for the reduced tree: recursively delete unlabelled leaves (with their incoming arcs), then suppress elementary nodes; two partially labelled trees have the same reduction iff they induce the same rooted triple on every three labels.

**Restricted LGT networks.** $N$ is *restricted* if (a) no principal child of a principally elementary node is principally elementary; (b) the target of a secondary arc is never principally elementary; (c) for every secondary arc $(u,h)$ there is no principal path $u \leadsto h$; and (d) for every secondary arc $(u,h)$ with $z = \mathrm{LCA}_{T_0(N)}(u,h)$, the principal path $z \leadsto h$ has some intermediate node that is not principally elementary.

**Distinctness.** In a restricted LGT network, $\tilde T_0(N) \ne \tilde T_e(N)$ for every secondary arc $e$, and $\tilde T_e(N) \ne \tilde T_{e'}(N)$ for distinct secondary arcs $e \ne e'$.

**Characterization (one transfer).** For phylogenetic trees $T, T'$ on the same labels, there is a restricted LGT network $N$ with a secondary arc $e$ such that $T = \tilde T_0(N)$ and $T' = \tilde T_e(N)$ if and only if (1) the rooted subtree-prune-and-regraft distance $d_{rSPR}(T,T') = 1$, and (2) for an rSPR operation that prunes the subtree rooted at $h$ and regrafts it at $w$ to produce $T'$, the node $w$ is neither an ancestor of $h$ nor a descendant of the parent of $h$ in $T$. Equivalent conditions on triples and on clusters can be checked, the latter in $O(n^2)$ time for $n = |S|$.

**Uniqueness.** If two restricted LGT networks with one secondary arc each have the same reduced principal subtree and the same reduced secondary subtree, they are equal. More generally, if $T, T'_1, \dots, T'_k$ are pairwise different and some restricted LGT network has reduced principal subtree $T$ and reduced secondary subtrees $T'_1,\dots,T'_k$, then this network is unique up to isomorphism and is constructed by combining the single-transfer networks $N(T, T'_i)$, each of which it contains.

## Depends on

- [Rooted SPR distance](../../../not-yet-classified/rooted-spragreement-forest/rspr-dist.md)
- [Rooted triplet](../../splits-compatibility-ultrametrics-and-upgma/triplet.md)
- [Cluster system displaying a triplet](../../splits-compatibility-ultrametrics-and-upgma/displays-triplet.md)

## Expansion

Condition (c) makes the principal clusters of $u$ and $h$ disjoint, and condition (d) supplies a node $w$ on $z \leadsto h$ with a principal child outside that path. Taking $x_1$ below $u$, $x_2$ below $h$ and $x_3$ below that child, $T_0$ induces the triple $((x_2,x_3),x_1)$ while $T_e$ induces $((x_1,x_2),x_3)$, so the reduced trees differ. Replacing the principal arc into $h$ by $e$ is exactly one prune-and-regraft of the subtree at $h$, giving $d_{rSPR} = 1$; conversely, from such an rSPR one adds the arc $(w,h)$ (splitting an arc above $w$ when the regraft is onto an arc) and conditions (1)–(2) translate back into (c)–(d). Conditions (a) and (b) are needed for uniqueness: without them two transfers from adjacent elementary nodes can be swapped without changing any secondary subtree.

## Sources

- G. Cardona, J. C. Pons, F. Rosselló, "A reconstruction problem for a class of phylogenetic networks with lateral gene transfers", Algorithms for Molecular Biology 10 (2015) 28, Definitions 1–2, Propositions 1–8 and Corollary 1, <https://doi.org/10.1186/s13015-015-0059-z>, PMCID PMC4683721.
