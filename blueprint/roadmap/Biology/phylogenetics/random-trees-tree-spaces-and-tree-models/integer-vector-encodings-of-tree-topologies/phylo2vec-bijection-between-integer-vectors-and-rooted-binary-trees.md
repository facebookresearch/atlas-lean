# Phylo2Vec bijection between integer vectors and rooted binary trees

**Statement.** Label the leaves of rooted binary trees on $n \ge 2$ taxa by $0, 1, \dots, n-1$. Let

$$\mathcal V_n = \big\{ v \in \mathbb Z^{n-1} : v[j] \in \{0, 1, \dots, 2(j-1)\} \text{ for } j = 1, \dots, n-1 \big\}.$$

Draw each rooted binary tree on $m \ge 2$ leaves $0, \dots, m-1$ with an extra edge above its root, and label its $2m - 1$ edges as follows (the branch labelling of the source's Fig. 2b):
- the pendant edge of leaf $i$ gets label $i$, for $i = 0, \dots, m-1$;
- the edge above the root gets label $2(m-1)$;
- the remaining $m - 2$ internal edges get labels $m, m+1, \dots, 2m-3$ in order: among the current cherries, take the one containing the highest leaf label, give the next label to the edge above that cherry, prune the cherry's higher-labelled leaf (its parent becomes a leaf carrying the lower label), and repeat.

Start from the tree with leaves $0$ and $1$ and then, for $j = 2, \dots, n-1$ in order, take the edge with label $v[j]$ in the labelled current tree on leaves $0, \dots, j-1$ and attach leaf $j$ by subdividing it (for $j = 1$, $v[1] = 0$ and the start tree is the cherry on $0$ and $1$); values $v[j] < j$ mean that leaf $j$ forms a cherry with leaf $v[j]$. This defines a map from $\mathcal V_n$ to labeled rooted binary tree topologies.

**Lemma 1.** This map is a bijection between $\mathcal V_n$ and the set of labeled rooted binary trees on $n$ leaves. In particular

$$|\mathcal V_n| = \prod_{j=1}^{n-1} (2j - 1) = (2n - 3)!!,$$

the number of rooted binary trees on $n$ labeled leaves.

**Birth-process subclass.** Restricting to $v[j] \in \{0, \dots, j-1\}$ gives the $(n-1)!$ trees in which every newly added leaf forms a cherry with an earlier leaf (an "ordered" tree). For $n \ge 3$, $(n-1)! < (2n-3)!!$, so this simpler encoding is not surjective; for $n = 2$ both sets have one member.

**Moves.** Changing one entry of $v$ moves the tree by a subtree prune-and-regraft-like operation, so there are $O(n^2)$ single-entry neighbors, and local search over $v$ explores the whole tree space.

## Expansion

When leaf $j$ is added, the current rooted tree on $j$ leaves has $2(j-1)$ edges plus a root edge, so there are $2j - 1$ attachment points; the labelling rule fixes which label each of them carries, which a count alone does not (with three leaves, exchanging the labels of the root edge and the other internal edge would give a different tree for the same entry). Each insertion is reversible: deleting the largest leaf and suppressing its parent recovers the previous tree and the index of the attachment edge. Hence the stepwise-addition map is injective, and since $\mathcal V_n$ and the tree set have the same cardinality $(2n-3)!!$, it is a bijection. This is the integer-vector version of the classical stepwise-addition argument for counting rooted trees, and it gives a compact, sampling-friendly coordinate system for tree topologies in likelihood-based phylogenetic search.

## Sources

- M. J. Penn, N. Scheidwasser, M. P. Khurana, D. A. Duchêne, C. A. Donnelly, S. Bhatt, "Phylo2Vec: A Vector Representation for Binary Trees", Systematic Biology 74(2) (2025) 250, Equations (1)-(2) and Appendix Lemma 1, <https://doi.org/10.1093/sysbio/syae030>, PMCID PMC11958935.
- J. Felsenstein, "The number of evolutionary trees", Systematic Zoology 27(1) (1978) 27-33, <https://doi.org/10.2307/2412810>.
