# Finite-ground positive program to DATA Datalog/Horn correspondence

This node collects the correspondence between finite ground definite (positive) logic programs and
positive Datalog programs read as propositional Horn clauses.

## Expansion

A sound expansion has separate pages for:

1. **Encoding.** A finite ground definite program is a finite set of rules $a \leftarrow b_1, \dots, b_m$
   over a finite atom set; each ground atom is read as a nullary Datalog predicate (or each program as
   the ground instantiation of a Datalog program over its active domain), giving the same rules.
2. **Semantics agree.** The least Herbrand model of the definite program, the least fixed point of its
   immediate-consequence operator $T_P$, and the least model of the corresponding Datalog program
   coincide; grounding over the active domain introduces no atoms outside it.
3. **Scope.** Rules with negative bodies are outside this correspondence; they are handled by the
   stable-model pages, not by the Datalog least-model theorem.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Finite ground normal logic programs.

## Depends on

- [Datalog programs and the immediate consequence operator](../../ComputerScience/databases/datalog/datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](../../ComputerScience/databases/datalog/least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- V. Lifschitz, *Twelve definitions of a stable model*, ICLP 2008, LNCS 5366, 37–51, Section 2.1: the least Herbrand model of a definite program (van Emden and Kowalski). <https://www.cs.utexas.edu/~vl/papers/12defs.pdf>
