# Coresets for directional width of size O(1/ε^d)

Let $P$ be a nonempty set of $n$ points in $\mathbb{R}^d$, for fixed $d$, and $0 < \varepsilon < 1$. In $O(n)$ time one can compute an $\varepsilon$-coreset of $P$ for directional width of size $O(1/\varepsilon^d)$. A single point is its own coreset. Otherwise let $r \ge 1$ be the dimension of the affine hull of $P$; since $W_P(u)$ depends only on the projection of $u$ onto the linear subspace parallel to that hull (orthogonal components cancel in differences), one works in the hull: after an affine map onto $\mathbb{R}^r$ that makes $P$ fat, which preserves ratios of directional widths, overlay a grid of cubes of diameter proportional to $\varepsilon$ and keep one point from each nonempty cube, giving $O(1/\varepsilon^r)$ points.

## Depends on

- [Coreset for directional width](coreset-for-directional-width.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 25, Lemma 1 (a linear transformation making $P$ $\alpha$-fat preserves directional-width coresets) and Theorem 2 (an $\varepsilon$-coreset of size $O(1/\varepsilon^d)$ in $O(n)$ time)
