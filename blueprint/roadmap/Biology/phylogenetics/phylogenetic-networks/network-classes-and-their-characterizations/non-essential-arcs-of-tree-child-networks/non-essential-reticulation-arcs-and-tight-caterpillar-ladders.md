# Non-essential reticulation arcs and tight caterpillar ladders

**Setting.** A rooted phylogenetic network $\mathcal{N}$ on a leaf set $X$ is a rooted acyclic digraph whose leaves are labeled by $X$; reticulations have in-degree two and out-degree one, and the remaining non-root, non-leaf vertices (tree vertices) have in-degree one and out-degree two. It is tree-child if every non-leaf vertex has a child that is a tree vertex or a leaf. An arc set $\mathcal{E}$ is an embedding of a rooted phylogenetic $X$-tree $\mathcal{T}$ if the subgraph it induces is a subdivision of $\mathcal{T}$, and $\mathcal{N}$ displays $\mathcal{T}$ if such an embedding exists. An arc $e$ is essential if some displayed $X$-tree has every embedding using $e$, and non-essential otherwise; deleting a non-essential arc (and cleaning up the resulting degree-two vertices) leaves the set of displayed trees unchanged. It suffices to study reticulation arcs: if a tree arc is non-essential, then some reticulation arc is non-essential as well.

**Caterpillar ladders.** For $X = \{\ell_0,\dots,\ell_k\}$, $k \ge 1$, the caterpillar ladder $\langle\ell_0,\ell_1,\dots,\ell_k\rangle$ is the tree-child network with spine

$$q_k, q_{k-1}, p_k, q_{k-2}, p_{k-1}, \dots, q_2, p_3, q_1, p_2, p_1$$

(a single arc $(q_1, p_1)$ when $k = 1$), an arc $(p_1, \ell_0)$, and for each $j$ a reticulation $v_j$ with parents $p_j$ and $q_j$ and child $\ell_j$. It is tight in $\mathcal{N}$ if there is an injective map $\phi$ fixing the leaves such that (P1) each pendant arc $(p_1, \ell_0)$ and $(v_j, \ell_j)$ maps to a tree path, (P2) each reticulation arc $(u, v_j)$ maps to an arc of $\mathcal{N}$, and (P3) each spine arc maps to an arc of $\mathcal{N}$. Its first rung is the arc $(\phi(p_1), \phi(v_1))$ and its last rung is $(\phi(q_k), \phi(v_k))$.

**Theorem.** Let $e$ be a reticulation arc of a tree-child network $\mathcal{N}$. Then $e$ is non-essential if and only if $e$ is the first or last rung of a tight caterpillar ladder of $\mathcal{N}$.

**Corollary.** If $\mathcal{N}$ is normal (tree-child without shortcuts), or level-1 with every underlying cycle of length at least four, then every reticulation arc of $\mathcal{N}$ is essential.

## Expansion

In a tree-child network an arc set is an embedding of a displayed tree exactly when it picks one parent arc per reticulation, so a reticulation arc is non-essential iff every tree using it is also displayed by some embedding avoiding it. In a tight ladder the spine arcs and rungs interlock so that any embedding using the first (or last) rung can be rerouted, by shifting the reticulation choices along the ladder, to an embedding of the same tree that avoids it. Conversely, starting from a non-essential arc one finds a short nearly-tight ladder and extends it, toward or away from the root, one rung at a time until properties (P1)–(P3) hold; tree-child structure rules out every other configuration. Normal networks have no shortcuts and hence no tight ladders, and in a level-1 network a tight ladder has a single reticulation whose cycle has length three.

## Sources

- Simone Linz and Charles Semple, "Non-essential arcs in phylogenetic networks", Journal of Computer and System Sciences 128 (2022), 1–17, <https://doi.org/10.1016/j.jcss.2022.02.005>; numbering as in arXiv:2107.07721: Lemma 2.1, Theorem 3.1 and Corollary 3.2.
