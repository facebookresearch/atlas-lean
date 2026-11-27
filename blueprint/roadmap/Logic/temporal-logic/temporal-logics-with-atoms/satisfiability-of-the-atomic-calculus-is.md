# Satisfiability of the atomic μ-calculus is undecidable

The modal μ-calculus with orbit-finite disjunctions over sets with atoms has an undecidable satisfiability problem, already in its scalar form.

**Theorem (Klin and Łełyk).** It is undecidable whether a given formula of the (scalar) [atomic μ-calculus](temporal-logics-over-sets-with-atoms.md) is satisfiable, that is, holds at some state of some atomic Kripke model. This holds both for equality atoms and for ordered atoms.

Classical μ-calculus satisfiability is decidable (EXPTIME-complete), and model checking of the vectorial atomic μ-calculus over orbit-finite models is decidable (Theorem 5.1 of the source).

## Depends on

- [Temporal logics over sets with atoms](temporal-logics-over-sets-with-atoms.md)

## Proof depends on

- [Satisfiability of atomic LTL is undecidable](satisfiability-of-atomic-ltl-is-undecidable.md)

## Expansion

An atomic LTL formula $\varphi$ in negation normal form is translated into an atomic μ-calculus formula $M(\varphi)$ by $M(\mathbf X\varphi) = \square M(\varphi)$, $M(\varphi\,\mathbf U\,\psi) = \mu Y.(M(\psi) \vee (M(\varphi) \wedge \square Y))$, $M(\varphi\,\mathbf R\,\psi) = \nu Y.(M(\psi) \wedge (M(\varphi) \vee \square Y))$, homomorphically on the other connectives. In a word model, $\varphi$ implies $M(\varphi)$; in any Kripke model, $M(\varphi)$ at a state implies $\varphi$ along every infinite path from it. Hence $\varphi$ is satisfiable iff $M(\varphi) \wedge \nu X.\lozenge X$ is, the second conjunct saying that an infinite path starts at the state.

## Sources

- B. Klin and M. Łełyk, "Scalar and Vectorial mu-calculus with Atoms", *Logical Methods in Computer Science* 15(4), 2019, paper 5, <https://doi.org/10.23638/LMCS-15(4:5)2019>; numbers from arXiv:1803.06752v3, <https://arxiv.org/abs/1803.06752v3>: Section 9: Theorem 9.2 and its proof; Theorem 5.1.
