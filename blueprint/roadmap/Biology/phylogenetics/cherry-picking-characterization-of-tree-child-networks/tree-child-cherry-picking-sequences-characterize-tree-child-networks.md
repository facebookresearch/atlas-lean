# Tree-child cherry-picking sequences characterize tree-child networks

**Definitions.** A rooted phylogenetic network on taxa $X$ is **tree-child** if every non-leaf vertex has a child that is not a reticulation; equivalently, it has no *stack* (a reticulation whose child is a reticulation) and no *sibling reticulations* (two reticulations sharing a parent). In a network, a pair of leaves $\{x, y\}$ is a **cherry** $[x,y]$ if they share a parent, and a **reticulated cherry** $(x,y)$ if the parent of $x$ is a reticulation whose other parent is the parent of $y$. Reducing a cherry deletes $x$ (and suppresses resulting degree-two vertices); reducing a reticulated cherry deletes the reticulation edge into $x$. A cherry-reduction sequence $\mathcal R = \mathcal R_0, \mathcal R_1, \dots, \mathcal R_k$ is **complete** if $\mathcal R_k$ is a single vertex; its cherry-picking sequence is $\Sigma = (r_1, \dots, r_k)$ with $r_i$ the reduced pair.

For $r_i$ containing first element $x_i$, let $s(i)$ be the smallest $j > i$ such that $r_j$ contains $x_i$ (the *successor pair* $S(i) = r_{s(i)}$), or $\infty$. $\Sigma$ is **tree-child** if
- (P1) every reticulated cherry $r_i = (x_i, y_i)$ with $s(i) < \infty$ has a successor that is a cherry $[x_j, y_j]$, and
- (P2) no pair is the successor of two distinct reticulated cherries.

The same notions are defined for unrooted phylogenetic networks.

**Theorem (rooted).** A rooted phylogenetic network is tree-child if and only if it has a complete tree-child cherry-picking sequence. Moreover, for a tree-child network every cherry-picking sequence associated with a complete cherry-reduction sequence is tree-child, and every maximal cherry-reduction sequence of an orchard network is complete.

**Theorem (unrooted).** An unrooted phylogenetic network is tree-child (has a tree-child orientation) if and only if it has a complete tree-child cherry-picking sequence. If $\mathcal R$ is a tree-child orientation of $\mathcal U$, then their reticulation numbers coincide: $r(\mathcal U) = r(\mathcal R)$.

## Expansion

Tree-child networks are orchard networks, so they can always be reduced to a single vertex by cherry picking. Condition (P1) encodes the absence of stacks: if after removing a reticulation edge the leaf $x$ next appears in a reticulated cherry, its parent was a reticulation directly below another reticulation. Condition (P2) encodes the absence of sibling reticulations: two reticulation edges whose removals both make the same pair available share a parent. The proof is by induction on the length of the sequence, peeling off the first reduction. Because the characterization never uses the root, it transfers verbatim to unrooted networks, giving a sequence-based recognition of unrooted tree-child networks.

## Sources

- J. Döcker, S. Linz, "Characterising rooted and unrooted tree-child networks", arXiv:2408.17105 (2024), Proposition 2.1 and Lemma 2.2 (Section 2), Lemmas 3.1–3.2, Theorems 3.3–3.4 and Corollary 3.5 (Section 3), <https://doi.org/10.48550/arXiv.2408.17105>.
