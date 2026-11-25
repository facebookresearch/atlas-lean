# Completeness of the Segerberg axioms for PDL

This node covers the axiomatization of propositional dynamic logic (PDL) with tests and its
completeness for the standard relational semantics.

Programs are built from atomic programs and tests $\varphi?$ by choice, composition and
iteration; in a model, iteration denotes the reflexive-transitive closure of the relation of its
argument and $\varphi?$ denotes the identity restricted to the worlds satisfying $\varphi$. The
Segerberg system has as axioms the instances of propositional tautologies and, writing
$\langle a \rangle \varphi$ for $\neg[a]\neg\varphi$:
$\langle a \rangle \varphi \wedge [a]\psi \to \langle a \rangle(\varphi \wedge \psi)$;
$\langle a \rangle(\varphi \vee \psi) \leftrightarrow \langle a \rangle \varphi \vee \langle a \rangle \psi$;
$\langle a \cup b \rangle \varphi \leftrightarrow \langle a \rangle \varphi \vee \langle b \rangle \varphi$;
$\langle a ; b \rangle \varphi \leftrightarrow \langle a \rangle \langle b \rangle \varphi$;
$\langle \psi? \rangle \varphi \leftrightarrow \psi \wedge \varphi$;
$\varphi \vee \langle a \rangle \langle a^* \rangle \varphi \to \langle a^* \rangle \varphi$; and the
induction axiom
$\langle a^* \rangle \varphi \to \varphi \vee \langle a^* \rangle(\neg\varphi \wedge \langle a \rangle \varphi)$.
Its rules are modus ponens and modal generalization, from $\varphi$ infer $[a]\varphi$. The main result: a formula is derivable in this system exactly
when it is valid in every model. PDL is not compact, so this is weak completeness, not
completeness for arbitrary sets of hypotheses.

## Depends on

- [PDL formulas](propositional-dynamic-logic-pdl/formula.md)
- [PDL programs](propositional-dynamic-logic-pdl/program.md)
- [PDL model](propositional-dynamic-logic-pdl/model.md)
- [Relation denoted by a PDL program](propositional-dynamic-logic-pdl/prog-rel.md)
- [Satisfaction of PDL formulas](propositional-dynamic-logic-pdl/sat.md)

## Expansion

A sound expansion has separate pages for:

1. the Segerberg system as a derivation relation on the PDL syntax, and soundness;
2. if completeness is obtained through another calculus or syntax, a semantics-preserving
   translation of all formulas and programs, including tests and nested iteration, and the
   correspondence between the two calculi, each stated separately;
3. the Fischer–Ladner closure and the finite model property;
4. weak completeness;
5. an executable decision procedure for satisfiability and validity with a proof of correctness and
   termination;
6. noncompactness.

A completeness proof for the test-free fragment does not cover the full syntax with tests; the
standard relational semantics (iteration as reflexive-transitive closure, tests as subrelations of
the identity) must be used, not arbitrary program-labeled models.

## Sources

- Cornell University, CS 6861 Handout B, *Propositional dynamic logic*, 6 April 2024: the
  Segerberg axioms and the noncompactness of PDL.
  <https://www.cs.cornell.edu/courses/cs6861/2024sp/Handouts/PDL.pdf>
- D. Kozen and R. Parikh, *An elementary proof of the completeness of PDL*, Theoretical Computer
  Science 14 (1981), 113–118; the proof there omits tests.
