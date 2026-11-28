# The art gallery problem is complete for the existential theory of the reals

The *art gallery problem* asks, for a simple polygon $P$ with integer vertex coordinates and an integer $k$, whether there is a set $G$ of $k$ points of $P$ such that every point of $P$ is seen by some $g \in G$, where $g$ sees $p$ if the segment $gp$ lies in $P$. The art gallery problem is complete for the complexity class $\exists\mathbb{R}$ under polynomial-time reductions: it is polynomial-time equivalent to deciding whether a system of polynomial equations with integer coefficients has a real solution. In particular it is not in NP unless $\mathrm{NP} = \exists\mathbb{R}$ (Abrahamsen, Adamaszek and Miltzow, Theorem 1). Separately, for polygons with rational vertex coordinates, for every real algebraic number $\alpha$ there is such a polygon in which every minimum guard set has a guard with $x$-coordinate $\alpha$ (Theorem 2); scaling the polygon to integer coordinates scales this coordinate as well.

## Depends on

- [Chvátal's art gallery theorem](chvatal-s-art-gallery-theorem.md)
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Expansion

This page becomes ready once:

- Definition prerequisite: the complexity class $\exists\mathbb{R}$ (problems polynomial-time reducible to the existential theory of the reals), which is not yet stated.
- Proof prerequisite: the problem ETR-INV, its $\exists\mathbb{R}$-completeness, and the reduction from ETR-INV to the art gallery problem, as pages of their own.

## Sources

- M. Abrahamsen, A. Adamaszek and T. Miltzow, "The art gallery problem is ∃ℝ-complete", arXiv:1704.06969, <https://arxiv.org/abs/1704.06969>: abstract (the problem statement, $\exists\mathbb{R}$-completeness, the consequence for NP, and the corollary on algebraic guard coordinates)
