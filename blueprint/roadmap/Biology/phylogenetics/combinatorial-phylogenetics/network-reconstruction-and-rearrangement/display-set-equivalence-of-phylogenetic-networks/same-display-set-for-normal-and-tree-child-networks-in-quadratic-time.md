# Polynomial-time equality of display sets for a normal and a tree-child network

A (binary) rooted phylogenetic network $\mathcal{N}$ on a leaf set $X$ is a rooted acyclic digraph with no parallel arcs in which the unique root has out-degree $2$, the vertices of out-degree $0$ have in-degree $1$ and form the leaf set $X$, and every other vertex is a tree vertex (in-degree $1$, out-degree $2$) or a reticulation (in-degree $2$, out-degree $1$); if $|X|=1$, the single vertex labelled by $X$ also counts. It is **tree-child** if every non-leaf vertex has a child that is a tree vertex or a leaf, and **normal** if it is tree-child and has no shortcut (no arc $(u,v)$ for which another directed path from $u$ to $v$ exists). The *display set* $T(\mathcal{N})$ is the set of rooted binary phylogenetic $X$-trees displayed by $\mathcal{N}$, i.e. obtained by deleting one incoming arc at each reticulation and suppressing degree-two vertices.

Deciding whether two arbitrary networks have the same display set is $\Pi_2^P$-complete.

**Theorem.** Let $\mathcal{N}$ be a normal network and $\mathcal{N}'$ a tree-child network on $X$. Deciding whether $T(\mathcal{N})=T(\mathcal{N}')$ can be done in time quadratic in $|X|$.

The algorithm rests on local structure that equal display sets force:

- If $\mathcal{N}'$ has no trivial shortcuts and $\{a,b\}$ is a cherry of $\mathcal{N}$ (siblings with a common tree-vertex parent), then $T(\mathcal{N})=T(\mathcal{N}')$ only if $\{a,b\}$ is a cherry of $\mathcal{N}'$.
- If $\{a,b\}$ is a reticulated cherry of $\mathcal{N}$ (the parent $p_b$ of $b$ is a reticulation and $(p_a,p_b)$ is an arc, where $p_a$ is the parent of $a$), equality of display sets forces $\{a,b\}$ to appear in $\mathcal{N}'$ either as the same reticulated cherry (with matching clusters below the other parent of the reticulation) or in one of two explicit configurations in which the parent of $b$ in $\mathcal{N}'$ is a tree vertex.

Repeatedly identifying such a pair, checking the forced configuration and reducing both networks (collapsing a cherry, or deleting the reticulation arc of a reticulated cherry) either exhibits a mismatch or reduces both networks to a single leaf.

## Expansion

1. Normal networks display a set of trees from which the network is uniquely recoverable, which is why one side must be normal.
2. Every tree-child network has a cherry or a reticulated cherry; the structural propositions translate a cherry or reticulated cherry of $\mathcal{N}$ into a necessary local configuration in $\mathcal{N}'$.
3. Each reduction preserves the equivalence "$T(\mathcal{N})=T(\mathcal{N}')$" and removes one leaf or one reticulation, and each check costs $O(|X|)$, giving $O(|X|^2)$ overall.

## Sources

- J. Doecker, S. Linz, C. Semple, *Display sets of normal and tree-child networks*, arXiv:1901.06725 (Section 1 definition of phylogenetic network, Theorem 1.1, Propositions 3.1, 3.3 and 3.4, Theorem 5.1). <https://doi.org/10.48550/arXiv.1901.06725> Published version: The Electronic Journal of Combinatorics, 28, Paper 1.8, 2021, <https://doi.org/10.37236/9128>.
