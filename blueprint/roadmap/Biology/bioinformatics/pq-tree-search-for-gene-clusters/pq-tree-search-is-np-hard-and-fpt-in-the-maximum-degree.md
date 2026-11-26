# PQ-tree search is NP-hard and fixed-parameter tractable in the maximum node degree

**Setting.** A **PQ-tree** $T$ on a set of leaves is a rooted ordered tree whose internal nodes are of two kinds. The children of a *P-node* may be permuted arbitrarily, and the children of a *Q-node* may only be reversed. The *frontier* $F(T)$ is the left-to-right sequence of leaf labels. In comparative genomics, a PQ-tree compactly encodes the set of gene orders observed for a gene cluster: its frontiers under all legal reorderings. For $d\ge0$, $T$ is **quasi-equivalent to $T'$ with limit $d$**, written $T\succeq_dT'$, if $T'$ arises from $T$ in three steps: permute the children of some P-nodes, reverse the children of some Q-nodes, then delete at most $d$ leaves and smooth away internal nodes left with fewer than two children. Write $C_d(T)=\{F(T'):T\succeq_dT'\}$.

**PQ-tree Search (decision).** The input is a PQ-tree $T$ with $m$ leaves labelled over $\Sigma_T$, $m_p$ P-nodes, $m_q$ Q-nodes and maximum node degree $\gamma$; a string (genome) $S\in\Sigma_S^n$; deletion limits $d_T,d_S\in\mathbb N$; and a Boolean substitution relation $h\subseteq\Sigma_S\times\Sigma_T$. The question is whether there is a one-to-one mapping between leaves of $T$ and characters of a substring $S'$ of $S$ that derives $T$ to $S'$ with at most $d_T$ leaves deleted from $T$ and at most $d_S$ characters deleted from $S'$. Here *derives* means: some frontier in $C_{d_T}(T)$, matched under $h$, is obtained from $S'$ by deleting at most $d_S$ characters. In the *optimization* version $h$ is a substitution score and deletions have costs; the goal is a highest-scoring such derivation.

**Theorem.**

1. PQ-tree Search is NP-hard.
2. The optimization version is solvable by dynamic programming in

$$O\big(n\,\gamma\,d_T^2d_S^2\,(m_p2^{\gamma}+m_q)\big)\ \text{time and}\ O\big(d_Td_S(mn+2^{\gamma})\big)\ \text{space}.$$

In particular PQ-tree Search is fixed-parameter tractable with parameter $\gamma$, with an $O^*(2^\gamma)$ algorithm, where $O^*$ hides factors polynomial in the input size.

By comparison, enumerating all reorderings costs $O\big(2^{m_q}(\gamma!)^{m_p}\,nm(d_T+d_S)d_Td_S\big)$. This is super-exponential in $\gamma$, and exponential in $m$ when all internal nodes are P-nodes.

## Expansion

*Hardness.* The reduction is from JISP3 (job interval selection with three candidate intervals per job, all of length $2$), which is NP-complete. Pick exactly one interval of each of $\gamma$ colors so that no two chosen intervals intersect. Intervals lie in $[1,L]$. Encode position $p$ as a character $\sigma_p$, and let $S=\sigma_1\sigma_a\sigma_b\sigma_2\sigma_a\sigma_b\cdots\sigma_a\sigma_b\sigma_L$. The tree has a P-node root with one Q-node child $x_i=(x_i^s,x_i^a,x_i^b,x_i^f)$ per color $i$, plus filler leaves that may match any character. The relation $h$ lets $x_i^s$ and $x_i^f$ match the start and end characters of any interval of color $i$, and lets $x_i^a,x_i^b$ match $\sigma_a,\sigma_b$. With $d_T=d_S=0$, a derivation exists iff the instance has a valid selection. So the problem is NP-hard even when no deletions are allowed.

*Algorithm.* The table $A[j,i,k_T,k_S]$ stores the best score of a derivation of the subtree rooted at node $x_j$ to a substring of $S$ starting at position $i$, with exactly $k_T$ tree deletions and $k_S$ string deletions. A Q-node's children must appear in one of two orders, so they are processed left to right, and in reverse, by a sequence-alignment–style DP over $(i,k_T,k_S)$. A P-node's children may appear in any order, so its DP runs over subsets $C$ of children already placed, at cost $2^{\gamma}$ per P-node. Leaves are scored by $h$. Correctness follows by induction on the tree, using the operations that add or remove one child derivation or one deleted character at either end of a partial derivation. Implemented on bacterial genomes, the search finds chromosomal gene-cluster orders rearranged in plasmids.

The statements are the NP-hardness theorem, the running-time lemma of the main algorithm, and the FPT theorem of the source.

## Sources

- G. R. Zimerman, D. Svetlitsky, M. Zehavi, M. Ziv-Ukelson, "Approximate Search for Known Gene Clusters in New Genomes Using PQ-Trees", arXiv:2007.03589 (2020). <https://doi.org/10.48550/arXiv.2007.03589>
