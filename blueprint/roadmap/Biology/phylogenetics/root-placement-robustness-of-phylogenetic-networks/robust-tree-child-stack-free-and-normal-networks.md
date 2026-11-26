# Robust tree-child, stack-free and normal networks

**Setting.** Let $N$ be a robustly orientable unrooted phylogenetic network: every root position on an edge admits an orientation that is a rooted phylogenetic network. For a class $\mathcal C$ of rooted networks, $N$ is *robustly $\mathcal C$* if every phylogenetic orientation for every root position belongs to $\mathcal C$. Recall that a rooted network is *tree-child* if every internal vertex has at least one child that is a tree vertex (in-degree 1), *stack-free* if every reticulation vertex has only tree children, and *normal* if it is tree-child and has no shortcut edges $(u,v)$ for which another directed path from $u$ to $v$ exists. A binary network is level-$k$ if each blob becomes a tree after removing at most $k$ edges.

**Theorem 3.6.** An unrooted binary phylogenetic network is level-$k$ with $k\le1$ if and only if every decorated blob (a blob with its incident cut-edges) is a simple cycle with exactly one cut-edge leading away from each cycle vertex.

**Theorem 4.1.** Every robustly orientable level-$k$ network with $k\le1$ is robustly tree-child and robustly stack-free.

**Theorem 4.6.** A robustly orientable level-$k$ network with $k\ge2$ is neither robustly tree-child nor robustly stack-free.

**Theorem 4.7.** For a robustly orientable network $N$ the following are equivalent: (1) $N$ is robustly tree-child; (2) $N$ is robustly stack-free; (3) $N$ is level-$k$ for some $k\le1$.

**Theorem 4.8.** A robustly orientable phylogenetic network is robustly normal if and only if it is an unrooted phylogenetic tree.

## Depends on

- [Robust orientability of unrooted phylogenetic networks](robust-orientability-of-unrooted-phylogenetic-networks.md)

## Expansion

In a level-1 network each blob is a cycle in which every vertex has a pendant cut-edge. Whatever the root, the cycle is entered at one vertex and has a unique sink, the single reticulation of that cycle, whose parents are two tree vertices; every cycle vertex has a non-reticulate child through its pendant cut-edge or along the cycle, giving tree-child and stack-free. Intuitively, in a blob of level at least $2$ one can choose a root position and orientation in which two reticulations are adjacent, so one is the parent of the other and both properties fail. Normality additionally forbids shortcuts, and in any cycle the root can be placed so that one of the two directed paths from the entry vertex to the reticulation is a single edge, which is a shortcut; only networks without cycles, that is trees, avoid this for every rooting.

## Sources

- T. Britz, M. Hendriksen, K. O'Reilly, "Classes of phylogenetic networks that are robust to root placement", arXiv preprint (2026), Theorems 3.6, 4.1, 4.6, 4.7 and 4.8, <https://doi.org/10.48550/arXiv.2607.15625>.
