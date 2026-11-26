# Polynomial-time reconstruction of a binary normal network from its display set

**Setting.** A binary normal network (tree-child, no shortcuts; see the companion article) with $k$ reticulations displays exactly $2^k$ binary phylogenetic $X$-trees, and a binary normal network is uniquely determined by its set of displayed binary trees, its **display set**. A collection $\mathcal{P}$ of binary phylogenetic $X$-trees is **tightly normal compatible** if it is exactly the display set of some binary normal network on $X$; then $|\mathcal{P}| = 2^k$ for some $k \ge 0$ and the network is unique with exactly $k$ reticulations.

**Theorem.** The following recursive algorithm (Display Set Compatibility) runs in polynomial time and, given a collection $\mathcal{P}$ of binary phylogenetic $X$-trees, correctly decides whether $\mathcal{P}$ is tightly normal compatible, in which case it returns the unique binary normal network whose display set is $\mathcal{P}$.

1. If $|\mathcal{P}|$ is not a power of two, reject. If $|X| \le 2$, return the unique tree on $X$.
2. If some $\{a,b\}$ is a cherry of every tree in $\mathcal{P}$: delete $b$ from every tree, recurse, and if a network $\mathcal{N}'$ is returned, re-attach $b$ as the sibling of $a$; otherwise reject.
3. Else, if some $\{a,b\}$ is a cherry of exactly half of the trees, forming $\mathcal{P}_1$, and for some $x \in \{a,b\}$ there is a bijection $\varphi : \mathcal{P}_1 \to \mathcal{P} - \mathcal{P}_1$ such that for every $\mathcal{T}_1 \in \mathcal{P}_1$ the pair $\{a,b\}$ is a reticulated cherry with reticulation leaf $x$ in the unique binary normal network with display set $\{\mathcal{T}_1,\varphi(\mathcal{T}_1)\}$: recurse on $\mathcal{P} - \mathcal{P}_1$; if a network $\mathcal{N}'$ is returned, subdivide the edges into $x$ and into $y$ ($\{y\} = \{a,b\} - \{x\}$) by new vertices $p_x, p_y$, add the edge $(p_y,p_x)$, and return the result if it is normal; otherwise reject.
4. Otherwise reject.

## Depends on

- [Normal cherry-picking sequences and the normal hybridisation number](normal-cherry-picking-sequences-and-the-normal-hybridisation-number.md)

## Expansion

Every binary normal network has a cherry or a reticulated cherry. A cherry $\{a,b\}$ of the network is a cherry of every displayed tree, and removing $b$ gives a normal network whose display set is the reduced collection (step 2). If instead $x$ is the child of a reticulation whose two parents lead to $x$'s partner $y$ and elsewhere, then the displayed trees split into two equal halves according to which reticulation edge is kept: in one half $\{x,y\}$ is a cherry, and pairing each such tree with the tree that differs only in that choice gives the bijection $\varphi$; the other half is the display set of the network with the reticulation edge from $y$'s side deleted, which is again normal (step 3). Because a binary normal network is determined by its display set, the recursion reconstructs it, and each step involves only polynomially many cherry and pairing checks. A failed check at any level certifies that no binary normal network has display set exactly $\mathcal{P}$.

## Sources

- Magnus Bordewich, Simone Linz and Charles Semple, "When is a set of phylogenetic trees displayed by a normal network?", arXiv:2407.06638 (2024), Section 3, Theorem 3.4, <https://doi.org/10.48550/arXiv.2407.06638>. Published version: Journal of Computer and System Sciences 160 (2026) 103811, <https://doi.org/10.1016/j.jcss.2026.103811>.
