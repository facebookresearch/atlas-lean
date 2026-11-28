# NP-hardness of tree-child network inference for line trees via permutation supersequences

**Setting.** A **line tree** (caterpillar) is a rooted binary phylogenetic tree in which every internal node other than the root has one or two leaf children. For a permutation string $P = p_1p_2\cdots p_n$ of an alphabet $\Sigma$ and an extra leaf $\ell$, $T(P,\ell)$ is the line tree with root $r$, path $r \to v_1 \to \dots \to v_n$, leaf $p_i$ hanging from $v_i$, and $\ell$ a second child of $v_n$. A tree-child network displaying a set of trees is **parsimonious** if it minimizes the hybridization number $\mathrm{HN}(N) = \sum_v (d^-(v) - 1)$ over all tree-child networks displaying them.

*Problems.* TCN: given trees $T_1,\dots,T_k$ on $X$ and an integer $h$, is there a tree-child network displaying all $T_j$ with $\mathrm{HN} \le h$? SCS: given strings and an integer $m$, is there a common supersequence of length at most $m$?

**Theorem.**

1. SCS is NP-hard even when every input string is a permutation of the alphabet.
2. Consequently TCN is NP-hard even when every input tree is a line tree: a parsimonious tree-child network for $T(P_1,\ell),\dots,T(P_k,\ell)$ yields, in linear time, a shortest common supersequence of $P_1,\dots,P_k$, and conversely.
3. The parsimonious tree-child networks displaying all line trees on $X$ coincide with those displaying all binary trees on $X$.
4. If $P$ is a parsimonious tree-child network displaying all binary trees on $X$, $n = |X| \ge 8$, then

$$\frac{(n-2)(n-1)(n+3)}{6} \le \mathrm{HN}(P) \le \frac{n^3 - 5n^2 + 21n - 53}{3}.$$

**Lemma (supersequences of all permutations).** For an $n$-letter alphabet $A$ with set of permutation strings $A_p$, the shortest common supersequence length is $1$, $3$ and $n^2 - 2n + 4$ for $n = 1$, $n = 2$ and $3 \le n \le 7$ respectively, and for $n \ge 8$

$$\frac{n(n+1)}{2} \le |\mathrm{SCS}(A_p)| \le n^2 - 2n + 4 - \left\lfloor \frac{n-7}{3} \right\rfloor.$$

## Depends on

- [Hybridisation number equals the minimum weight of a leaf-added cherry-picking sequence](../leaf-added-cherry-picking-sequences/hybridisation-number-equals-minimum-leaf-added-cherry-picking-weight.md)

## Expansion

Parsimonious tree-child networks for trees $T_1,\dots,T_k$ can be built from an ordering $\pi$ of the taxa: in each tree, label the root by the smallest taxon and every other internal node $u$ by the larger of the minimal taxa below its two children; each taxon $f$ then labels a unique internal node $w$, and the **lineage taxon string** (LTS) of $f$ lists the labels of the internal nodes on the path from $w$ to $f$. A parsimonious network is assembled from shortest common supersequences $\gamma_i$ of the LTSs of $\pi_i$ across the trees, with $\mathrm{HN} = \sum_{i=1}^n |\gamma_i| - n + 1$. For the line trees $T(P_j,\ell)$ and a suitable ordering, the LTSs encode the permutations $P_j$, so minimizing $\mathrm{HN}$ is exactly finding a shortest common supersequence of the permutations; NP-hardness of SCS for permutations transfers. For all binary trees versus all line trees, the sets of LTSs of each taxon have the same shortest common supersequence (both contain all strings of distinct letters of maximal length), which gives item 3, and summing the bounds of the lemma over the taxa gives item 4.

## Sources

- Laurent Bulteau and Louxin Zhang, "The tree-child network problem for line trees and the shortest common supersequences for permutations", arXiv:2307.04335 (2023), Theorems 1–6 and the lemma on supersequences of all permutations (Section 6), <https://doi.org/10.48550/arXiv.2307.04335>. Published version: Journal of Computer and System Sciences 144 (2024) 103546, <https://doi.org/10.1016/j.jcss.2024.103546>.
