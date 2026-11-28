# Whether a free formula holds for matrices of some size is undecidable

No algorithm decides, given a closed first-order formula built from positivity conditions of Hermitian free polynomials evaluated at Hermitian matrices, whether the formula holds for matrices of at least one size, although for each fixed size it is decidable.

**Setting (Drescher, Netzer and Thom).** Let $\mathbb{C}\langle x_1, \dots, x_n\rangle$ be the algebra of polynomials in non-commuting variables, with the involution fixing each $x_i$ and conjugating scalars, and let $\mathbb{M}_d(\mathbb{C}\langle x_1, \dots, x_n\rangle)_h$ be the Hermitian $d \times d$ matrix polynomials. Such a $p$ can be evaluated at any tuple $(A_1, \dots, A_n)$ of Hermitian $s \times s$ complex matrices, the result being a Hermitian $ds \times ds$ matrix; set $W_s(p) = \{A : p(A) \succeq 0\}$ and $O_s(p) = \{A : p(A) \succ 0\}$ (positive semidefinite, respectively positive definite). A *free formula* is a first-order formula whose atomic formulas are the conditions $A \in W(p)$ and $A \in O(p)$, combined by Boolean connectives and quantifiers over tuples of Hermitian matrices (the source uses this notion without a formal grammar); for a fixed size $s$ every quantified variable ranges over Hermitian $s \times s$ matrices, so a closed free formula $\varphi$ is either true or false at each size $s$. So that inputs are finite objects, the coefficients of the polynomials in an input formula are taken in the Gaussian rationals $\mathbb{Q}(i)$: the source names no coefficient field for its decision problem, and the formulas expressing unitary representations of finitely presented groups, with a unitary matrix written as $A + iB$ for Hermitian $A, B$, need no other coefficients.

**Theorem (Drescher, Netzer and Thom).** The question whether a free closed formula holds for at least one size of matrices is undecidable (Theorem 2.1 of arXiv:1709.08424v1). Its proof exhibits a recursively enumerable sequence of free closed formulas $(\varphi_i)_{i \in \mathbb{N}}$ for which no algorithm decides, given $i$, whether $\varphi_i$ holds for some size $s$.

For each fixed free closed formula $\varphi$, the set of sizes $s$ at which $\varphi$ holds is recursive, because at a fixed size the formula becomes a first-order formula over the real closed field $\mathbb{R}$, to which quantifier elimination applies (Remark 2.2 of the source). The theorem is an obstruction to a projection theorem for free semialgebraic sets: unlike in the commutative case, projections cannot in general be described algorithmically by quantifier-free free formulas.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Quantifier elimination yields quantifier-free formulas](../../../../Logic/model-theory/quantifier-elimination-for-real-closed-fields/is-qf-qe.md)
- [Quantifier elimination preserves truth](../../../../Logic/model-theory/quantifier-elimination-for-real-closed-fields/holds-qe.md)
- [Malcev's theorem on linear groups](../../../../GroupTheory/linear-groups/malcev-residually-finite.md)

## Expansion

Bridson and Wilton constructed a recursively enumerable sequence of finitely presented groups $(G_i)$ for which the set of $i$ such that $G_i$ has a nontrivial finite-dimensional unitary representation is not recursive. The source observes that the statement that $G_i$ has a nontrivial unitary representation is easily expressed as a free closed formula $\varphi_i$, true at size $s$ exactly when $G_i$ has a nontrivial unitary representation of dimension $s$; equalities of matrices are intersections of semidefiniteness conditions. So deciding whether $\varphi_i$ holds at some size would decide the Bridson–Wilton property. A complete expansion links a page for Bridson and Wilton's theorem that it is undecidable whether a finitely presented group has a nontrivial finite quotient, equivalently a nontrivial finite-dimensional unitary representation. The equivalence uses Malcev's theorem, linked above: the image of a nontrivial finite-dimensional unitary representation is a nontrivial finitely generated linear group, hence residually finite, so the group has a nontrivial finite quotient; conversely, the regular representation of a nontrivial finite quotient is a nontrivial unitary representation. The two quantifier-elimination results linked above give the decidability at each fixed size, not the undecidability across sizes.

## Sources

- T. Drescher, T. Netzer and A. Thom, "On projections of free semialgebraic sets", *Advances in Geometry* 23(2):207–214, 2023, doi:[10.1515/advgeom-2022-0021](https://doi.org/10.1515/advgeom-2022-0021); read as arXiv:1709.08424v1 ([arXiv](https://arxiv.org/abs/1709.08424v1)), whose numbering is used: the setting of Section 1, Theorem 2.1 with its proof and Remark 2.2.
