# Global satisfiability over elementary frame classes

For a first-order sentence Φ about a binary relation, the elementary modal logic of Φ is unimodal logic over the Kripke frames satisfying Φ; its global satisfiability problem asks whether a modal formula holds at every world of some model on such a frame.

**Definition.** Let $\Phi$ be a first-order sentence, possibly with equality, over the signature $\{R\}$ of one binary relation symbol, and let $\mathcal K_\Phi$ be the class of Kripke frames $(W, R)$, with $W$ nonempty, satisfying $\Phi$; on an empty set of worlds every formula would hold globally. $\Phi$ is *universal* if it has the form $\forall x_1 \cdots \forall x_n\,\psi$ with $\psi$ quantifier-free. A unimodal formula $\varphi$ (built from propositional variables by Boolean connectives and $\lozenge$, with $\square = \neg\lozenge\neg$) is *globally satisfiable* over $\mathcal K_\Phi$ if there are a frame $(W, R) \in \mathcal K_\Phi$ and a valuation such that $\varphi$ holds at every world of $W$, and *finitely globally satisfiable* if moreover $W$ can be chosen finite. The problems $\mathcal K_\Phi$-SAT and $\mathcal K_\Phi$-FINSAT ask, for a given modal formula, whether it is globally satisfiable, respectively finitely globally satisfiable, over $\mathcal K_\Phi$; here $\Phi$ is fixed and the modal formula is the input.

Global satisfiability of $\varphi$ over $\mathcal K_\Phi$ amounts to first-order satisfiability of $\Phi \wedge \forall x\,\mathrm{st}_x(\varphi)$, where $\mathrm{st}$ is the standard translation, so both problems are decidable when $\Phi$ is a two-variable sentence: $\Phi \wedge \forall x\,\mathrm{st}_x(\varphi)$ is then a two-variable sentence, and that fragment is decidable and has the finite model property. Membership of $\Phi$ alone in a decidable fragment does not suffice, since the conjunction can leave it: every universal sentence lies in the decidable Bernays–Schönfinkel–Ramsey class, yet some universal $\Phi$ give undecidable problems (Theorem 5 of the source). For frame classes defined by universal Horn sentences, such as the reflexive, transitive, symmetric or Euclidean frames, local satisfiability of modal formulas is decidable, in PSPACE, by results the source cites.

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)
- [Modal formulas](../kripke-semantics/formula.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [First-order language of Kripke frames](../standard-translation-of-modal-logic/frame-language.md)
- [A frame as a first-order structure](../standard-translation-of-modal-logic/frame-structure.md)

## Proof depends on

None.

## Expansion

Abbreviations such as $\deg_{\ge m}(x)$, "$x$ has at least $m$ distinct $R$-successors", can be used inside universal sentences when they occur negatively, by introducing universally quantified fresh variables; a world is *ramified* in the source's constructions if its out-degree is at least $7$. A modal formula may have only infinite models over $\mathcal K_\Phi$: if $\Phi$ forces irreflexivity and transitivity, $\lozenge p \wedge \square\lozenge p$ has no finite model.

## Sources

- J. Michaliszyn, J. Otop and P. Witkowski, "Satisfiability vs. Finite Satisfiability in Elementary Modal Logics", in *Proceedings of the Third International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2012)*, Electronic Proceedings in Theoretical Computer Science 96, 2012, pp. 141–154, <https://doi.org/10.4204/EPTCS.96.11>; numbers from arXiv:1210.2481v1, <https://arxiv.org/abs/1210.2481v1>: Section 1 (elementary modal logics, global satisfiability, the standard translation, universal Horn classes) and Section 2 (the abbreviation $\deg_{\ge m}$).
