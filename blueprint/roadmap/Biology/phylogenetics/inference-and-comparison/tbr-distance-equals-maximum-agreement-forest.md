# Reductions and fixed-parameter tractability of the TBR distance

For unrooted binary trees $T_1, T_2$ on the same leaf set, let $m(T_1, T_2)$ be the maximum agreement forest number, which equals the tree bisection and reconnection distance $d_{\mathrm{TBR}}(T_1, T_2)$ by [the theorem of Allen and Steel](../../not-yet-classified/tbragreement-forest/tbr-dist-eq-maf-number.md) (2001, Theorem 2.13). Allen and Steel (2001) further prove: the subtree prune and regraft distance satisfies $d_{\mathrm{SPR}} \ge m$ (inequality (2.6)), and the inequality can be strict; the subtree reduction (Rule 1) and the chain reduction (Rule 2, replacing a chain of at least three subtrees common to both trees by three leaves) preserve the TBR distance (Theorem 3.4); and the parameterized TBR-distance problem is fixed-parameter tractable (Theorem 3.8), because by Lemmas 3.6 and 3.7 maximally reduced trees at TBR distance $k$ have at most $4c(k - 1)$ leaves for a constant $c$, independent of the number of leaves of the original trees.

## Depends on

- [TBR distance equals the maximum agreement forest number](../../not-yet-classified/tbragreement-forest/tbr-dist-eq-maf-number.md)

## Expansion

1. Subtree prune and regraft moves, the inequality $d_{\mathrm{SPR}} \ge m$, and an example where it is strict.
2. Theorem 3.4: invariance of the TBR distance under Rules 1 and 2, using Lemma 2.11 on induced subtrees.
3. Theorem 3.8: the degree bound of Lemma 3.6, the leaf bound of Lemma 3.7, and fixed-parameter tractability.
4. NP-hardness of the TBR-distance problem from the proof of Theorem 8 of Hein, Jiang, Wang and Zhang combined with Theorem 2.13, as a separate statement.

## Sources

- B. L. Allen and M. Steel, Subtree transfer operations and their induced metrics on evolutionary trees, Ann. Comb. 5 (2001), 1–15, Definition 2.12, Theorems 2.13, 3.4 and 3.8. <https://doi.org/10.1007/s00026-001-8006-8>
