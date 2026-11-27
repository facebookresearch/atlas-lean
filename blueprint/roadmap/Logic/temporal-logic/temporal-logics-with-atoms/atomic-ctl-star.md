# Atomic CTL*

Atomic CTL* extends CTL* by disjunctions over orbit-finite sets of formulas, built from basic propositions that may mention atoms, and is interpreted over atomic Kripke models.

**Definition.** Over atoms $\mathbb A$ and an equivariant set $P$ of basic propositions as in [atomic Kripke models](atomic-kripke-models.md), *atomic CTL** has state formulas $\Phi ::= p \mid \bigvee\Psi \mid \neg\Phi \mid \exists\varphi$ and path formulas $\varphi ::= \Phi \mid \bigvee\Psi' \mid \neg\varphi \mid \varphi\,\mathbf U\,\varphi \mid \mathbf X\varphi$, where $\Psi$ and $\Psi'$ range over orbit-finite sets of state and path formulas respectively. State formulas are evaluated at states of an atomic Kripke model and path formulas along its infinite paths, as for CTL*, an orbit-finite disjunction holding iff some disjunct does. The path quantifier $\exists$ may range over all paths or over finitely supported paths only; the source allows either reading.

## Depends on

- [Atomic Kripke models](atomic-kripke-models.md)
- [State formulas of CTL$^{\ast}$](../ctl/ctl-state-and-path-formulas/state-formula.md)

## Proof depends on

None.

## Expansion

Classical CTL* embeds into the modal μ-calculus, but this fails with atoms: model checking the vectorial atomic μ-calculus over orbit-finite models is decidable, while model checking atomic CTL* is not.

## Sources

- B. Klin and M. Łełyk, "Scalar and Vectorial mu-calculus with Atoms", *Logical Methods in Computer Science* 15(4), 2019, paper 5, <https://doi.org/10.23638/LMCS-15(4:5)2019>; numbers from arXiv:1803.06752v3, <https://arxiv.org/abs/1803.06752v3>: Section 2 (Definition 2.5) and Section 4 (the paragraph introducing atomic CTL* and LTL, and the design choice for path quantifiers after Definition 4.7).
