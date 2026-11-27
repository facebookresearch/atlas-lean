# Correspondence between node-based and stem-based trees

**Definitions.** A rooted tree $T$ has edges directed from parent to child, written $x \to y$. A tree is *planted* if its root has exactly one child. Given a rooted tree $T$ on $n$ vertices labelled $1,\dots,n$ (any of which may be the root), **Algorithm A** builds a tree $U$: add a new root labelled $0$ with an edge $0 \to \mathrm{root}(T)$; label each edge $v \to w$ by the label $w$ of its child; erase the vertex labels. **Algorithm B** reverses this for a planted tree $U$ with $n$ edges labelled $1,\dots,n$: label each non-root vertex by the label of its parent edge, erase edge labels, and delete the root $r$ and its edge $r \to s$, making $s$ the root.

**Theorem.** Algorithms A and B are mutually inverse bijections between
1. rooted trees on $n$ vertices labelled $1,\dots,n$ (node-based trees), and
2. planted trees on $n+1$ vertices with edges labelled $1,\dots,n$ (stem-based trees).
The algorithms work unchanged in the presence of polytomies. Under this bijection, the vertex sets of subtrees of $T$ correspond exactly to the edge sets of **planted** subtrees of $U$ (and proper subtrees to proper planted subtrees); the edge set of a non-planted subtree of $U$ does not, in general, correspond to a subtree of $T$.

**Consequence for monophyly.** A monophyletic group (an ancestor with all its descendants) is a subtree (clade below a vertex) of a node-based tree and a planted subtree (clade below a stem edge) of a stem-based tree. Applying a vertex-based clade definition to a stem-based tree can produce a non-monophyletic group, so the "node-based" and "stem-based" clade definitions describe the same groups once each is applied to its own tree type.

## Expansion

Algorithm A creates exactly one edge per original vertex, each labelled by its child endpoint, so $U$ has $n$ labelled edges and $n+1$ vertices, and the new root has the single child $\mathrm{root}(T)$, so $U$ is planted. Algorithm B undoes each step: labels return from parent edges to child vertices and the added root is removed. Because a vertex $v$ of $T$ becomes the edge entering the image of $v$, a vertex set closed under taking descendants of its top vertex corresponds to that edge together with everything below it, which is a planted subtree. Character data attached to edges of a stem-based tree likewise transfer to vertex labels of the node-based tree.

## Sources

- J. Martin, D. Blackburn, E. O. Wiley, "Are node-based and stem-based clades equivalent? Insights from graph theory", PLoS Currents Tree of Life (2010), Algorithms A and B, Theorem 1 and the discussion of monophyly, <https://doi.org/10.1371/currents.RRN1196>, PMCID PMC2989695.
