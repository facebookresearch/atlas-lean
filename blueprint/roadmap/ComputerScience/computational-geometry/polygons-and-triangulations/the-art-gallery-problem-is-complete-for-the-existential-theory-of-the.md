# The art gallery problem is complete for the existential theory of the reals

The *art gallery problem* asks, for a simple polygon $P$ with integer vertex coordinates and an integer $k$, whether there is a set $G$ of $k$ points of $P$ such that every point of $P$ is seen by some $g \in G$, where $g$ sees $p$ if the segment $gp$ lies in $P$. The art gallery problem is complete for the complexity class $\exists\mathbb{R}$ under polynomial-time reductions: it is polynomial-time equivalent to deciding whether a system of polynomial equations with integer coefficients has a real solution. In particular it is not in NP unless $\mathrm{NP} = \exists\mathbb{R}$, and for every real algebraic number $\alpha$ there is an instance in which some guard of every minimum guard set has a coordinate equal to $\alpha$ (Abrahamsen, Adamaszek and Miltzow).

## Depends on

- [Chvátal's art gallery theorem](chvatal-s-art-gallery-theorem.md)
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Expansion

This page becomes ready once:

- Definition prerequisite: the complexity class $\exists\mathbb{R}$ (problems polynomial-time reducible to the existential theory of the reals), which is not yet stated.
- Source check: the full paper (beyond its abstract) has not been opened; the reduction should be checked there before formalization.

## Sources

- M. Abrahamsen, A. Adamaszek and T. Miltzow, "The art gallery problem is ∃ℝ-complete", arXiv:1704.06969, <https://arxiv.org/abs/1704.06969>: abstract (the problem statement, $\exists\mathbb{R}$-completeness, the consequence for NP, and the corollary on algebraic guard coordinates)
