# Unrooted SPR distance and the maximum agreement forest number

For unrooted binary trees $T_1, T_2$ on the same leaf set, let $m(T_1, T_2)$ be the maximum agreement forest number, which equals the tree bisection and reconnection distance $d_{\mathrm{TBR}}(T_1, T_2)$ by [the theorem of Allen and Steel](../../../not-yet-classified/tbragreement-forest/tbr-dist-eq-maf-number.md) (2001, Theorem 2.13). Allen and Steel (2001) further prove that the subtree prune and regraft distance satisfies $d_{\mathrm{SPR}}(T_1, T_2) \ge m(T_1, T_2)$ (inequality (2.6)), and that the inequality can be strict. Their reduction results for the TBR distance (Theorems 3.4 and 3.8: the subtree and chain reductions preserve the distance, and maximally reduced trees have linearly many leaves in the distance, so the problem is fixed-parameter tractable) are the unrooted two-tree case of the [linear kernel for maximum agreement forest on multiple trees](linear-kernel-for-maximum-agreement-forest-on-multiple-trees.md) and are not restated here.

## Depends on

- [TBR distance equals the maximum agreement forest number](../../../not-yet-classified/tbragreement-forest/tbr-dist-eq-maf-number.md)

## Expansion

1. Subtree prune and regraft moves, the inequality $d_{\mathrm{SPR}} \ge m$, and an example where it is strict.
2. NP-hardness of the TBR-distance problem from the proof of Theorem 8 of Hein, Jiang, Wang and Zhang combined with Theorem 2.13, as a separate statement.

## Sources

- B. L. Allen and M. Steel, Subtree transfer operations and their induced metrics on evolutionary trees, Ann. Comb. 5 (2001), 1–15, Definition 2.12, inequality (2.6) and Theorem 2.13. <https://doi.org/10.1007/s00026-001-8006-8>
