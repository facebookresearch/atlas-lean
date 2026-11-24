# Public announcement logic

Extend the multi-agent epistemic language with formulas $[F!]G$. In a Kripke model $M = (W, R, V)$ with one accessibility relation $R_a$ per agent, $M, w \models [F!]G$ holds if $M, w \not\models F$ or $M[F!], w \models G$, where $M[F!]$ restricts $M$ to the worlds satisfying $F$: its worlds are $\{v \in W : M, v \models F\}$ and each $R_a$ and the valuation are restricted to them. The following reduction laws are valid:

- $[F!]p \leftrightarrow (F \to p)$ for propositional letters $p$;
- $[F!](G \wedge H) \leftrightarrow ([F!]G \wedge [F!]H)$;
- $[F!]\neg G \leftrightarrow (F \to \neg [F!]G)$;
- $[F!][a]G \leftrightarrow (F \to [a][F!]G)$.

Using them, every formula of the language with announcements but without common knowledge is equivalent to an announcement-free formula, computed by rewriting innermost announcements first; so this public announcement logic has the same expressive power as the underlying epistemic logic, and its axiomatization by the reduction laws over a complete epistemic logic is sound and complete. With common knowledge added, no such reduction exists.

## Depends on

- [Epistemic models](model.md)

## Sources

- A. Baltag and B. Renne, "Dynamic epistemic logic", *Stanford Encyclopedia of Philosophy*, the language and semantics of public announcement logic, the axiomatic theory PAL with its reduction axioms, the PAL Reduction Theorem, PAL soundness and completeness, and the theorem that PAL with common knowledge admits no reduction, <https://plato.stanford.edu/entries/dynamic-epistemic/>
- The Open Logic Project, *The Open Logic Text*, complete build, release 2e19d09 (2026), Sections 57.7 and 57.8, Definition 57.11, <https://builds.openlogicproject.org/open-logic-complete.pdf>
