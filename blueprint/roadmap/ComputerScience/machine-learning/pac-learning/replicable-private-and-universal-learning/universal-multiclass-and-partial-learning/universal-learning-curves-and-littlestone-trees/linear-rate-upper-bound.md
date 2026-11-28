# Classes with no infinite VCL tree are learnable at linear rate

Let $X$ be a Polish space and $H \subseteq \{0,1\}^X$ a measurable class (in the sense of the source) with no infinite VCL tree. Then $H$ is learnable at rate $1/n$: there is a learner such that for every realizable $P$ there is $C > 0$ (depending on $P$) with $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \le C/n$ for all $n \ge 1$.

## Proof sketch

In a second Gale–Stewart game the adversary presents tuples of growing length together with labellings, and wins if every finite stage stays consistent with $H$; an infinite VCL tree is exactly a winning strategy for the adversary, so here the learner has a winning strategy, universally measurable under the measurability assumption. Played on i.i.d. data, this strategy learns after finitely many steps a pattern-avoidance function $g : X^t \to \{0,1\}^t$: with probability tending to one the target never produces the labelling $g(z_1, \dots, z_t)$ on any $t$ distinct sample points. The one-inclusion graph predictor of Haussler, Littlestone and Warmuth for the class of labellings avoiding $g$, whose restriction to the sample shatters no $t$ points, then has leave-one-out error below $t/n$; estimating a suitable $t$ from the first half of the sample and applying this predictor to the second half gives $\mathbb{E}[\mathrm{er}_P(\hat h_n)] = O(1/n)$ with a constant depending on $P$.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [VCL trees and the VCL dimension](vcl-tree.md)

## Proof depends on

- [Gale–Stewart theorem, open case](../../../../../../SetTheory/determinacy/gale-stewart-games/determined-of-is-open.md)
- [Haussler-Littlestone-Warmuth expected error bound for the one-inclusion predictor](../../../sample-complexity-and-combinatorial-dimensions/packing-and-one-inclusion-graphs/one-inclusion-predictor-error-bound.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Section 5 (Lemmas 5.2, 5.3, 5.8 and 5.10, Theorem 5.6).
