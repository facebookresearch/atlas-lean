# Combinatorial characterization of the three universal rates

Let $X$ be a Polish space and $H \subseteq \{0,1\}^X$ a measurable class (in the sense of the source) with $|H| \ge 3$. Then exactly one of the following holds:

- $H$ has no infinite Littlestone tree, and $H$ is learnable with optimal rate $e^{-n}$;
- $H$ has an infinite Littlestone tree but no infinite VCL tree, and $H$ is learnable with optimal rate $1/n$;
- $H$ has an infinite VCL tree, and $H$ requires arbitrarily slow rates.

For example, every finite class with at least three concepts and the thresholds $\{\mathbf{1}[x \ge t] : t \in \mathbb{N}\}$ on $\mathbb{N}$ (which have unbounded Littlestone dimension) have optimal rate $e^{-n}$; the thresholds $\{\mathbf{1}[x \ge t] : t \in \mathbb{R}\}$ on $\mathbb{R}$ have optimal rate $1/n$; and every class of finite VC dimension with at least three concepts is learnable at rate $1/n$.

The hypothesis $|H| \ge 3$ excludes only degenerate cases: if $|H| = 1$ or $H = \{h, 1-h\}$, error $0$ is achievable for every $n$, and if $|H| = 2$ otherwise, $H$ is learnable with optimal rate $e^{-n}$.

## Proof sketch

Combine the exponential upper and lower bounds, the linear lower bound for classes with an infinite Littlestone tree, the linear upper bound for classes with no infinite VCL tree, and the arbitrarily slow lower bound for classes with an infinite VCL tree. An infinite VCL tree contains an infinite Littlestone tree (keep the first point of each node and follow only the children whose label vanishes outside the first coordinate), so the three cases are exhaustive and mutually exclusive. Thresholds on $\mathbb{R}$ admit an infinite Littlestone tree by repeated bisection but have VC dimension one, hence no infinite VCL tree; for thresholds on $\mathbb{N}$, once a root point $x$ is chosen, the subtree in which the target is $1$ at $x$ leaves at most $x + 1$ concepts, so there is no infinite Littlestone tree.

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

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Theorems 1.6 and 1.9, footnote 2, Examples 2.1 and 2.2.
