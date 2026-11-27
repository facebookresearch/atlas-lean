# Lexicographic-linear ranking functions over the rationals are decidable in polynomial time

The problem $\mathrm{LexLinRF}(\mathbb{Q})$, whether a rational multipath [linear-constraint loop](linear-constraint-loops.md) has a [lexicographic-linear ranking function](lexicographic-linear-ranking-functions.md) in the permissive sense in which components need only be nonnegative up to the component that ranks a transition, is decidable in polynomial time. A polynomial-time procedure based on linear programming decides whether a *weak* LLRF exists, one whose components may decrease by any positive amount, and every weak LLRF can be turned into an LLRF.

## Depends on

- [Lexicographic-linear ranking functions](lexicographic-linear-ranking-functions.md)
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [Linear-constraint loops](linear-constraint-loops.md)

## Proof depends on

- [Weak LLRFs yield LLRFs over the rationals](weak-llrfs-yield-llrfs-over-the-rationals.md)
- [Linear programs are solvable in polynomial time](../../../../Geometry/convex-geometry/polynomial-time-linear-programming/linear-programs-are-solvable-in-polynomial-time.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 5.3, Lemma 5.26 (procedure LLRFSYN is sound and complete for weak LLRFs) and the theorem that $\mathrm{LexLinRF}(\mathbb{Q})$ is PTIME-decidable (Theorem 5.36 in arXiv:1208.4041v4).
