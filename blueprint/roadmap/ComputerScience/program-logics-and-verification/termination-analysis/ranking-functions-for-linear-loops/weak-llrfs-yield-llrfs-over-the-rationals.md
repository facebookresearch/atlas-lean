# Weak LLRFs yield LLRFs over the rationals

Let $Q_1, \dots, Q_k$ be the transition polyhedra of a rational multipath [linear-constraint loop](linear-constraint-loops.md). Procedure LLRFSYN of Ben-Amram and Genaim, which repeatedly solves linear programs to find an affine function that is nonnegative and non-increasing on all remaining transitions and strictly decreasing on as many of them as possible, and removes the transitions it ranks, is sound and complete for [weak LLRFs](weak-lexicographic-linear-ranking-functions.md): it returns a weak LLRF of minimal dimension (at most $n$) when one exists, and reports failure otherwise. From such a weak LLRF $\langle \rho_1, \dots, \rho_d \rangle$ one can construct in polynomial time affine functions $f_1, \dots, f_d$ such that

$$\langle f_1, f_2 + 1, \dots, f_d + d - 1 \rangle$$

is a [lexicographic-linear ranking function](lexicographic-linear-ranking-functions.md) for $Q_1, \dots, Q_k$ of the same dimension. Consequently a rational multipath loop has an LLRF if and only if it has a weak LLRF.

## Depends on

- [Weak lexicographic-linear ranking functions](weak-lexicographic-linear-ranking-functions.md)
- [Lexicographic-linear ranking functions](lexicographic-linear-ranking-functions.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", arXiv:1208.4041v4, 2025, <https://arxiv.org/abs/1208.4041v4>, Section 5.3, Lemma 5.26 (soundness and completeness of LLRFSYN), Lemma 5.31 (polynomial-time construction of $f_1, \dots, f_d$), Definition 5.32, Lemma 5.33 and Lemma 5.34.
