# Soundness and completeness of public announcement logic

Extend the multi-agent epistemic language with formulas $[F!]G$. In a Kripke model $M = (W, R, V)$ with one accessibility relation $R_a$ per agent, $M, w \models [F!]G$ holds if $M, w \not\models F$ or $M[F!], w \models G$, where $M[F!]$ restricts $M$ to the worlds satisfying $F$: its worlds are $\{v \in W : M, v \models F\}$ and each $R_a$ and the valuation are restricted to them. Public announcement logic is axiomatized over a sound and complete axiomatization of multi-agent epistemic logic by the reduction axioms

- $[F!]p \leftrightarrow (F \to p)$ for propositional letters $p$;
- $[F!]\bigl(G \wedge H\bigr) \leftrightarrow ([F!]G \wedge [F!]H)$;
- $[F!]\neg G \leftrightarrow (F \to \neg [F!]G)$;
- $[F!][a]G \leftrightarrow (F \to [a][F!]G)$;
- $[F!][H!]K \leftrightarrow [(F \wedge [F!]H)!]K$,

together with replacement of provable equivalents. This axiomatization is sound and complete for the language with announcements and without common knowledge.

## Depends on

- [Epistemic models](../model.md)
- [Epistemic formulas](../formula.md)
- [Satisfaction in an epistemic model](../sat.md)

## Proof depends on

- [Reduction law for announced atoms](reduction-law-for-announced-atoms.md)
- [Announcements distribute over implication](announcements-distribute-over-implication.md)
- [Reduction law for knowledge after an announcement](reduction-law-for-knowledge-after-an-announcement.md)
- [Composition of announcements](composition-of-announcements.md)
- [Announcement elimination](announcement-elimination.md)
- [The announcement translation is free of announcements and common knowledge](the-announcement-translation-is-announcement-free.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- A proof system for multi-agent epistemic logic and its soundness and completeness over epistemic models, the base logic the reduction axioms extend (proof prerequisite)

## Sources

- A. Baltag and B. Renne, "Dynamic epistemic logic", *Stanford Encyclopedia of Philosophy*, the language and semantics of public announcement logic, the axiomatic theory PAL with its reduction axioms, the PAL Reduction Theorem and PAL soundness and completeness, <https://plato.stanford.edu/entries/dynamic-epistemic/>
- The Open Logic Project, *The Open Logic Text*, complete build, release 2e19d09 (2026), Sections 57.7 and 57.8, Definition 57.11, <https://builds.openlogicproject.org/open-logic-complete.pdf>
