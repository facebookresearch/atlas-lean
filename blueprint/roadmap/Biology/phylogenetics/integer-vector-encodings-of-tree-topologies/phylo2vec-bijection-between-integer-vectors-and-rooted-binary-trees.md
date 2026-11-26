# Phylo2Vec bijection between integer vectors and rooted binary trees

**Statement.** Label the leaves of rooted binary trees on $n \ge 2$ taxa by $0, 1, \dots, n-1$. Let
$$\mathcal V_n = \big\{ v \in \mathbb Z^{n-1} : v[j] \in \{0, 1, \dots, 2(j-1)\} \text{ for } j = 1, \dots, n-1 \big\}.$$
Building the tree by adding leaves $1, 2, \dots, n-1$ in order, where the entry $v[j]$ selects one of the $2j - 1$ edges of the current rooted tree on leaves $0, \dots, j-1$ (counting the edge above the root) to which leaf $j$ is attached, with values $v[j] < j$ meaning that leaf $j$ forms a cherry with leaf $v[j]$, defines a map from $\mathcal V_n$ to labeled rooted binary tree topologies.

**Lemma 1.** This map is a bijection between $\mathcal V_n$ and the set of labeled rooted binary trees on $n$ leaves. In particular
$$|\mathcal V_n| = \prod_{j=1}^{n-1} (2j - 1) = (2n - 3)!!,$$
the number of rooted binary trees on $n$ labeled leaves.

**Birth-process subclass.** Restricting to $v[j] \in \{0, \dots, j-1\}$ gives the $(n-1)!$ trees in which every newly added leaf forms a cherry with an earlier leaf (an "ordered" tree), so this simpler encoding is not surjective.

**Moves.** Changing one entry of $v$ moves the tree by a subtree prune-and-regraft-like operation, so there are $O(n^2)$ single-entry neighbors, and local search over $v$ explores the whole tree space.

## Expansion

When leaf $j$ is added, the current rooted tree on $j$ leaves has $2(j-1)$ edges plus a root edge, so there are $2j - 1$ attachment points and each insertion is reversible: deleting the largest leaf and suppressing its parent recovers the previous tree and the index of the attachment edge. Hence the stepwise-addition map is injective, and since $\mathcal V_n$ and the tree set have the same cardinality $(2n-3)!!$, it is a bijection. This is the integer-vector version of the classical stepwise-addition argument for counting rooted trees, and it gives a compact, sampling-friendly coordinate system for tree topologies in likelihood-based phylogenetic search.

## Sources

- M. J. Penn, N. Scheidwasser, M. P. Khurana, D. A. Duchêne, C. A. Donnelly, S. Bhatt, "Phylo2Vec: A Vector Representation for Binary Trees", Systematic Biology 74(2) (2025) 250, Equations (1)-(2) and Appendix Lemma 1, <https://doi.org/10.1093/sysbio/syae030>, PMCID PMC11958935.
- J. Felsenstein, "The number of evolutionary trees", Systematic Zoology 27(1) (1978) 27-33, <https://doi.org/10.2307/2412810>.
