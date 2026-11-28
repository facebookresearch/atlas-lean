# Atomic LTL

Atomic LTL extends linear temporal logic by disjunctions over orbit-finite sets of formulas, built from basic propositions that may mention atoms, and is interpreted over deterministic atomic Kripke models.

**Definition.** Over atoms $\mathbb A$ and an equivariant set $P$ of basic propositions as in [atomic Kripke models](atomic-kripke-models.md), formulas of *atomic LTL* are $\varphi ::= p \mid \bigvee\Phi \mid \neg\varphi \mid \varphi\,\mathbf U\,\varphi \mid \mathbf X\varphi$, where $\Phi$ ranges over orbit-finite sets of formulas; this is the fragment of atomic CTL* without $\exists$. Formulas are interpreted at states of deterministic atomic Kripke models, in which every state has exactly one successor and so determines an infinite path, as in LTL, an orbit-finite disjunction holding iff some disjunct does.

## Depends on

- [Atomic Kripke models](atomic-kripke-models.md)
- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

A satisfiable atomic LTL formula can force its models to encode an unbounded sequence of distinct atoms, which is how it simulates the tape of a Turing machine.

## Sources

- B. Klin and M. Łełyk, "Scalar and Vectorial mu-calculus with Atoms", *Logical Methods in Computer Science* 15(4), 2019, paper 5, <https://doi.org/10.23638/LMCS-15(4:5)2019>; numbers from arXiv:1803.06752v3, <https://arxiv.org/abs/1803.06752v3>: Section 2 (the paragraph defining LTL as a fragment of CTL*) and Section 4 (the paragraph introducing atomic CTL* and LTL).
