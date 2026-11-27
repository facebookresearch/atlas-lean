# Coresets for directional width of size O(1/ε^d)

Let $P$ be a nonempty set of $n$ points in $\mathbb{R}^d$, for fixed $d$, and $0 < \varepsilon < 1$. In $O(n)$ time one can compute an $\varepsilon$-coreset of $P$ for directional width of size $O(1/\varepsilon^d)$: after an affine transformation that makes $P$ fat within its affine hull, which preserves ratios of directional widths (a $P$ contained in a hyperplane is handled in its affine hull, since its width is $0$ in the normal directions), overlay a grid of cubes of diameter proportional to $\varepsilon$ and keep one point from each nonempty cube.

## Depends on

- [Coreset for directional width](coreset-for-directional-width.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 25, Lemma 1 (a linear transformation making $P$ $\alpha$-fat preserves directional-width coresets) and Theorem 2 (an $\varepsilon$-coreset of size $O(1/\varepsilon^d)$ in $O(n)$ time)
