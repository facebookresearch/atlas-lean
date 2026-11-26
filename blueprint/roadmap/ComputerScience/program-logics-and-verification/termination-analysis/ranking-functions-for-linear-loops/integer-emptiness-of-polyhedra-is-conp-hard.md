# Integer emptiness of polyhedra is coNP-hard

The problem of deciding, given $B \in \mathbb{Z}^{m \times n}$ and $b \in \mathbb{Z}^m$, whether the polyhedron $\{x : Bx \le b\}$ contains no integer point is [coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)-hard. It remains coNP-hard for bounded polyhedra whose integer points lie in $\{0, 1\}^n$, by the reduction from satisfiability of a CNF formula in which each variable is bounded by $0$ and $1$ and each clause becomes one inequality.

## Depends on

- [The class coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [Unsatisfiability is coNP-complete](../../../../TheoryOfComputation/completeness-other-classes/unsatisfiability/unsat-conp-complete.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 3.1, proof of Theorem 3.1 and the note after it (citing R. M. Karp, "Reducibility among combinatorial problems", 1972).
