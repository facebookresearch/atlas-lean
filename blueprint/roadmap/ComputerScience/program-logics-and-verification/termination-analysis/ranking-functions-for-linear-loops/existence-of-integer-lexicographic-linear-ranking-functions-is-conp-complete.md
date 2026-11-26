# Existence of integer lexicographic-linear ranking functions is coNP-complete

The problem $\mathrm{LexLinRF}(\mathbb{Z})$, whether an integer multipath [linear-constraint loop](linear-constraint-loops.md) has a [lexicographic-linear ranking function](lexicographic-linear-ranking-functions.md), is coNP-complete. Hardness holds already for SLC loops and follows from the reduction for linear ranking functions; membership in coNP uses a witness of polynomial bit-size made of integer points and rays of the integer hulls of the transition polyhedra. For multipath loops in which each path belongs to one of the special classes with integral or efficiently computable integer hulls, the problem is decidable in polynomial time.

## Expansion

This page becomes ready once these prerequisites are stated:

- Integer hulls of rational polyhedra and the bounds on the bit-size of their generators (proof prerequisite)
- The coNP-hardness of $\mathrm{LinRF}(\mathbb{Z})$ for SLC loops, in a form that transfers to LLRFs (proof prerequisite)

## Depends on

- [Lexicographic-linear ranking functions](lexicographic-linear-ranking-functions.md)
- [The class coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [Linear-constraint loops](linear-constraint-loops.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 5.2 (hardness) and Theorem 5.23 (membership in coNP); Theorem 5.14 (polynomial-time special cases).
