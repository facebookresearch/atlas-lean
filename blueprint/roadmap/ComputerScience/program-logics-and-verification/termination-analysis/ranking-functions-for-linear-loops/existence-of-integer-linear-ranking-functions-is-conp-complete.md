# Existence of integer linear ranking functions is coNP-complete

The problem $\mathrm{LinRF}(\mathbb{Z})$, whether an integer multipath [linear-constraint loop](linear-constraint-loops.md) has a [linear ranking function](linear-ranking-functions.md), is coNP-complete. It is strongly coNP-hard already for SLC loops with affine-linear updates whose variables are restricted to a finite range, and it is in coNP for multipath loops: the absence of an LRF has a witness made of finitely many integer points of the transition polyhedra and rays of the recession cones of their integer hulls, which can be chosen of polynomial bit-size and together rule out every candidate LRF. An LRF, when one exists, can be synthesized in deterministic exponential time by computing integer hulls.

## Expansion

This page becomes ready once these prerequisites are stated:

- Integer hulls of rational polyhedra and the bounds on the bit-size of their generators (proof prerequisite)
- The coNP-hard problem used in the reduction for hardness (proof prerequisite)

## Depends on

- [Linear ranking functions](linear-ranking-functions.md)
- [The class coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [Linear-constraint loops](linear-constraint-loops.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 3, Theorem 3.1 (strong coNP-hardness), Theorem 3.12 (membership for SLC loops) and Theorem 3.17 (membership for MLC loops).
