# TBR distance equals the maximum agreement forest number

For unrooted binary trees $T_1, T_2$ on the same leaf set $L$, an agreement forest is a collection $\{t_1, \dots, t_k\}$ of binary trees whose leaf sets partition $L$, with $t_j = T_1|L(t_j) = T_2|L(t_j)$ for every $j$ and with the subtrees $T_i(L(t_j))$ vertex-disjoint in $T_i$ for $i = 1, 2$; let $m(T_1, T_2)$ be the minimum of $|F| - 1$ over agreement forests $F$ (Definition 2.12). Allen and Steel (2001, Theorem 2.13) prove $d_{\mathrm{TBR}}(T_1, T_2) = m(T_1, T_2)$ for the tree bisection and reconnection distance; in particular $m$ is a metric, and $d_{\mathrm{SPR}} \ge m$ (inequality (2.6)), which can be strict. They show (Theorem 3.4) that the subtree reduction (Rule 1) and the chain reduction (Rule 2, replacing a chain of at least three subtrees common to both trees by three leaves) preserve the TBR distance, and deduce (Theorem 3.8) that the parameterized TBR-distance problem is fixed-parameter tractable: by Lemmas 3.6 and 3.7, maximally reduced trees at TBR distance $k$ have at most $4c(k - 1)$ leaves for a constant $c$, a bound independent of the number of leaves of the original trees.

## Expansion

1. Definitions: tree bisection and reconnection (TBR) and subtree prune and regraft (SPR) moves on unrooted binary trees, and agreement forests.
2. Theorem 2.13: $m \le d_{\mathrm{TBR}}$ by induction on the distance, and $d_{\mathrm{TBR}} \le m$ by realizing a maximum agreement forest one TBR move at a time; the counterexamples to the corresponding claim for SPR.
3. Theorem 3.4: invariance of the TBR distance under Rules 1 and 2, using Lemma 2.11 on induced subtrees.
4. Theorem 3.8: the degree bound of Lemma 3.6, the leaf bound of Lemma 3.7, and fixed-parameter tractability.
5. NP-hardness of the TBR-distance problem from the proof of Theorem 8 of Hein, Jiang, Wang and Zhang combined with Theorem 2.13, as a separate statement.

## Sources

- B. L. Allen and M. Steel, Subtree transfer operations and their induced metrics on evolutionary trees, Ann. Comb. 5 (2001), 1–15, Definition 2.12, Theorems 2.13, 3.4 and 3.8. <https://doi.org/10.1007/s00026-001-8006-8>
