# Weak LLRFs yield LLRFs over the rationals

Let $Q_1, \dots, Q_k$ be the transition polyhedra of a rational multipath [linear-constraint loop](linear-constraint-loops.md). Procedure LLRFSYN of Ben-Amram and Genaim, which repeatedly solves linear programs to find an affine function that is nonnegative and non-increasing on all remaining transitions and strictly decreasing on as many of them as possible, and removes the transitions it ranks, is sound and complete for [weak LLRFs](weak-lexicographic-linear-ranking-functions.md): it returns a weak LLRF of minimal dimension (at most $n$) when one exists, and reports failure otherwise. From such a weak LLRF $\langle \rho_1, \dots, \rho_d \rangle$ one can construct affine functions $f_1, \dots, f_d$ such that

$$\langle f_1, f_2 + 1, \dots, f_d + d - 1 \rangle$$

satisfies, for some positive constants $\delta_1, \dots, \delta_d$, the conditions of a [lexicographic-linear ranking function](lexicographic-linear-ranking-functions.md) for $Q_1, \dots, Q_k$ with the required decrease $1$ at component $i$ replaced by $\delta_i$; multiplying it by any $c \ge 1 / \min_i \delta_i$ gives a lexicographic-linear ranking function of the same dimension. Consequently a rational multipath loop has an LLRF if and only if it has a weak LLRF.

## Depends on

- [Weak lexicographic-linear ranking functions](weak-lexicographic-linear-ranking-functions.md)
- [Lexicographic-linear ranking functions](lexicographic-linear-ranking-functions.md)
- [Linear-constraint loops](linear-constraint-loops.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 5.3, Lemma 5.26 (soundness and completeness of LLRFSYN), Definition 5.27 and Lemma 5.29 (construction of $f_1, \dots, f_d$), then the decrements $\delta_i$, the lemmas that the shifted functions form an LLRF, and the example that follows (Definition 5.32, Lemmas 5.33 and 5.34 and Example 5.35 in arXiv:1208.4041v4, whose Lemma 5.31, a polynomial-time implementation of the construction, is not in the journal version).
