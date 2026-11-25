# Soundness of differential dynamic logic including differential invariants

The proof calculus of differential dynamic logic, consisting of the dL axioms for the program constructs, the differential axioms
(differential invariants, differential cuts, differential weakening and differential ghosts) with their side conditions, and
uniform substitution with its admissibility conditions, is sound for hybrid programs with differential equations: every
provable formula is valid, that is, true in every state under every interpretation of its function, predicate and program
symbols, in the semantics of differential-form dL. That semantics extends the hybrid-program semantics of the definition
page: states also assign values to differential symbols $x'$, which along a continuous evolution hold the time derivatives
of the evolving variables, and terms include differentials $(\theta)'$. The calculus and its side conditions are those of
Platzer's uniform substitution calculus (its Figures 2 and 3). That the KeYmaera X prover implements this calculus with a
small soundness-critical core is a remark of the overview source, not part of the theorem.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Differential-form dL: differential symbols, differentials and interpretations of uninterpreted symbols.

## Depends on

- [Hybrid programs and differential dynamic logic semantics](hybrid-programs-and-differential-dynamic-logic-semantics.md)

## Proof depends on

- [Soundness of the discrete dynamic-logic fragment of dL](soundness-of-the-discrete-dynamic-logic-fragment-of-dl.md)

## Sources

- Overview of Logical Foundations of Cyber-Physical Systems — A. Platzer, Carnegie Mellon University (arXiv 1910.11232). <https://arxiv.org/pdf/1910.11232> Sec. 4.3 (soundness of the dL calculus) and Sec. 4.4 (soundness-critical core of KeYmaera X).
- A Uniform Substitution Calculus for Differential Dynamic Logic — A. Platzer, arXiv:1503.01981 (journal version in Journal of Automated Reasoning, 2017). <https://arxiv.org/pdf/1503.01981> Definitions 2–6 (syntax and semantics), Definition 12 (admissible uniform substitution), Figures 2 and 3 (axioms, including DW, DC, DE, DI and DG), Theorem 10 (soundness of uniform substitution) and Theorem 14 (soundness of the axioms and proof rules).
