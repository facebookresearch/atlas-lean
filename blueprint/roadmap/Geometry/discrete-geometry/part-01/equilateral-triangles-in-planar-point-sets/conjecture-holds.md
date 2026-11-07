# Erdős Problem 755 holds (Clemen–Dumitrescu–Liu)

Let $T_1(n)$ be the largest number of unit
equilateral triangles spanned by a set of $n$ points in $\mathbb{R}^6$, and let $T(n)$ be the
largest number of equilateral triangles of positive side length spanned by a set of $n$ points in
$\mathbb{R}^6$; a triangle spanned by a set is a three-element subset of it whose points are
pairwise at the same distance. Then there is a function $o : \mathbb{N} \to \mathbb{R}$ with
$o(n) \to 0$ as $n \to \infty$ such that $T_1(n) \le (1/27 + o(n))\, n^3$ for all sufficiently
large $n$, and $T(n)$ is asymptotically equivalent to $n^3/27$ as $n \to \infty$.

## Sources

- Felix Christian Clemen, Adrian Dumitrescu, and Dingyuan Liu, The number of regular simplices in higher dimensions, arXiv:2507.19841 (2025), https://arxiv.org/abs/2507.19841. Moved from `OpenConjectures/Geometry/ErdosProblem755`. Resolved true: Resolved externally by Clemen, Dumitrescu, and Liu. This repository records the statement, not an internal proof; a separate pinned Lean proof is cited in the registry.
