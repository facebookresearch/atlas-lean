# Realizability of HyperQPTL with one universal trace quantifier is undecidable

Realizability of HyperQPTL formulas with a single universal trace quantifier is undecidable as soon as the formula leaves the fragment $\exists_{q/\pi}^*\forall_q^*\forall_\pi Q_q^*$; in particular a universal-then-existential block of propositional quantifiers before the trace quantifier suffices.

**Theorem (Finkbeiner, Hahn, Hofmann and Tentrup).** The [realizability problem](realizability-of-hyperqptl-formulas.md) is undecidable for [HyperQPTL](hyperqptl.md) formulas with a single universal trace quantifier $\forall_\pi$ that lie outside the fragment $\exists_{q/\pi}^*\forall_q^*\forall_\pi Q_q^*$ (any existential trace or propositional quantifiers, then universal propositional quantifiers, then $\forall_\pi$, then arbitrary propositional quantifiers). In particular realizability is undecidable for the formulas of the form $\forall_q^*\exists_q^*\forall_\pi\,\psi$.

Realizability is decidable on the fragment $\exists_{q/\pi}^*\forall_q^*\forall_\pi Q_q^*$ itself (Theorem 3 of the source), so the boundary is tight for formulas with one universal trace quantifier. With several universal trace quantifiers realizability is undecidable in general, already for HyperLTL, because distributed architectures can be encoded (Corollary 3).

## Depends on

- [HyperQPTL](hyperqptl.md)
- [Realizability of HyperQPTL formulas](realizability-of-hyperqptl-formulas.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

A formula with one universal trace quantifier outside the decidable fragment either has a universal trace quantifier followed by an existential one, where undecidability is inherited from HyperLTL realizability (Finkbeiner, Hahn, Lukert, Stenger and Tentrup), or contains $\forall_q^*\exists_q^*\forall_\pi$. For the latter the proof reduces the Post correspondence problem: the universally quantified propositions $q_i, \vec{q}$ and the existentially quantified $p_i, \vec{p}$ simulate a universally and an existentially quantified trace of the strategy tree, and the body, following Finkbeiner and Hahn's $\forall\exists$ construction for HyperLTL, forces the strategy to write a sequence of dominoes on the relevant branches, each existential copy extending the universal one by one domino, so that the formula is realizable iff the instance has a solution.

## Sources

- B. Finkbeiner, C. Hahn, J. Hofmann and L. Tentrup, "Realizing ω-regular hyperproperties", in *Computer Aided Verification (CAV 2020)*, Lecture Notes in Computer Science 12225, Springer, 2020, pp. 40–63, doi:10.1007/978-3-030-53291-8_4; read as arXiv:2101.07161v1, <https://arxiv.org/abs/2101.07161v1>: Theorem 4 of arXiv:2101.07161v1 and its proof, which recalls the undecidability of HyperLTL realizability for a universal-then-existential prefix from Finkbeiner, Hahn, Lukert, Stenger and Tentrup; Theorem 3 and Corollary 3 (the numbering of that version, with separate counters per environment).
