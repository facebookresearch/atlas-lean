# Combinatorial characterization of the three universal rates

Let $H \subseteq \{0,1\}^X$ have at least three concepts and satisfy the measurability assumptions of the source. Then exactly one of the following holds:

- $H$ has no infinite Littlestone tree, and its optimal universal rate is $e^{-n}$;
- $H$ has an infinite Littlestone tree but no infinite VCL tree, and its optimal universal rate is $1/n$;
- $H$ has an infinite VCL tree, and $H$ requires arbitrarily slow rates.

For example, every finite class has optimal rate $e^{-n}$, the thresholds $\{\mathbf{1}[x \ge a] : a \in \mathbb{N}\}$ on $\mathbb{N}$ have optimal rate $1/n$, and every class of finite VC dimension has rate at least as fast as $1/n$.

Classes with one or two concepts are excluded because they are degenerate: for them the error can be zero after finitely many samples, so under the source's conventions they are not counterexamples to the trichotomy.

## Proof sketch

Combine the exponential upper and lower bounds, the linear lower bound for classes with an infinite Littlestone tree, the linear upper bound for classes with no infinite VCL tree, and the arbitrarily slow lower bound for classes with an infinite VCL tree. An infinite VCL tree contains an infinite Littlestone tree (take the first coordinate of each tuple), so the three cases are exhaustive and mutually exclusive. Thresholds on $\mathbb{N}$ admit an infinite Littlestone tree by binary search but have VC dimension one, so no infinite VCL tree.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)
- [VCL trees and the VCL dimension](vcl-tree.md)

## Proof depends on

- [Classes with no infinite Littlestone tree are learnable at exponential rate](exponential-rate-upper-bound.md)
- [No class with three concepts is learnable faster than exponentially](exponential-rate-lower-bound.md)
- [An infinite Littlestone tree forbids rates faster than linear](infinite-littlestone-tree-linear-lower-bound.md)
- [Classes with no infinite VCL tree are learnable at linear rate](linear-rate-upper-bound.md)
- [An infinite VCL tree forces arbitrarily slow universal rates](infinite-vcl-tree-arbitrarily-slow.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
