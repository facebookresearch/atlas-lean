# Semilinear sets are the sets definable in Presburger arithmetic

A set $X \subseteq \mathbb{N}^k$ is [semilinear](../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md) if and only if there is a formula $\varphi(x_1, \dots, x_k)$ of Presburger arithmetic, the first-order theory of $(\mathbb{N}, 0, +, <)$, such that $X = \{ (n_1, \dots, n_k) \mid \mathbb{N} \models \varphi(n_1, \dots, n_k) \}$; both translations are effective.

## Depends on

- [Semilinear set of vectors](../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)
## Proof depends on

- [Quantifier elimination for Presburger arithmetic](../../../../Logic/model-theory/quantifier-elimination-for-presburger-arithmetic.md)

## Expansion

This page becomes ready once the rest of its proof is linked:

- semilinear sets are closed under union, intersection, complement and projection (S. Ginsburg and E. H. Spanier, "Semigroups, Presburger formulas, and languages", *Pacific Journal of Mathematics* 16(2):285–296, 1966), so that a set defined by a quantifier-free formula with linear inequalities and congruences, and hence by any formula after quantifier elimination, is semilinear (proof prerequisite)
- the converse translation, which defines a linear set with root $r$ and periods $q$ by the existential formula $\exists \lambda\, (x = r + \sum_q \lambda_q q)$ and a semilinear set by the disjunction of these (proof)

## Sources

- J. Leroux, "The general vector addition system reachability problem by Presburger inductive invariants", *Logical Methods in Computer Science* 6(3:22), 2010, <https://arxiv.org/abs/1009.1076>, the abstract and Section 1 (semilinear sets, "a.k.a. the sets definable in Presburger arithmetic").
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, the paragraph after Theorem 3.2.24 (checking that a semilinear set is an inductive invariant reduces to Presburger arithmetic), p. 66.
- S. Ginsburg and E. H. Spanier, "Semigroups, Presburger formulas, and languages", *Pacific Journal of Mathematics* 16(2):285–296, 1966, Theorem 1.3 (p. 288): the Presburger sets of $\mathbb{N}^n$ are exactly the semilinear sets, and each description is effectively calculable from the other.
