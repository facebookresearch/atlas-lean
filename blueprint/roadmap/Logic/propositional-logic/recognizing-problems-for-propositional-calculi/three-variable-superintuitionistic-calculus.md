# Some superintuitionistic propositional calculus with three-variable axioms is undecidable

There is an intuitionistic propositional formula $A$ in three variables such that the calculus obtained from intuitionistic propositional logic by adding $A$ as an axiom has an undecidable set of theorems; counting the variables in all axioms of the calculus, three is the least possible number.

**Setting.** Formulas are built from propositional variables, $\bot$, $\wedge$, $\vee$ and $\to$. $\mathbf{Int}$ is the [calculus](propositional-calculi-with-modus-ponens-and.md) of intuitionistic propositional logic, with modus ponens and substitution as rules, sound and complete for [Kripke semantics](../intuitionistic-propositional-logic/kripke-models-for-ipc.md) on partially ordered frames. For a formula $A$, $\mathbf{Int} + A$ is the calculus obtained by adding $A$ as an axiom; every finitely axiomatized superintuitionistic propositional calculus has this form. A calculus is *undecidable* if no algorithm decides, for a given formula, whether it is derivable.

**Theorem (Bokov).** There is an intuitionistic propositional formula $A$ in three variables such that $\mathbf{Int} + A$ is undecidable (Theorem 3.1 of the source).

Measured by the number of variables in all axioms of a calculus with modus ponens and substitution, three is minimal: no axiomatization in which every axiom has at most two variables derives all intuitionistic tautologies, and every calculus with one-variable axioms is decidable (Gladstone), as the source recalls. Whether $\mathbf{Int} + A$ can be undecidable for a two-variable formula $A$ is not settled by this argument. The earlier undecidable superintuitionistic calculi of Shehtman (1978) and Chagrov (1994) used axioms in seven and four variables.

## Depends on

- [Propositional calculi with modus ponens and substitution](propositional-calculi-with-modus-ponens-and.md)
- [Kripke models for intuitionistic propositional logic](../intuitionistic-propositional-logic/kripke-models-for-ipc.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof encodes configurations $\langle s, m, n\rangle$ of a Minsky machine by superintuitionistic formulas in three variables, builds a Kripke model refuting the codes of derivable configurations (in the sense of Section 3.3 of the source), and encodes the instructions of the machine $\mathcal{M}$ by a single formula $A_{\mathcal{M}}$. A configuration is reachable if and only if its code is derivable in $\mathbf{Int} + A_{\mathcal{M}}$; choosing a machine and a start configuration with undecidable configuration problem (Minsky) gives an undecidable calculus.

## Sources

- Grigoriy V. Bokov, "On the number of variables in undecidable superintuitionistic propositional calculi", *Logic Journal of the IGPL* 24(5):774–791, 2016, doi:[10.1093/jigpal/jzw018](https://doi.org/10.1093/jigpal/jzw018). Numbering of the version read, arXiv:1504.03358v2: Theorem 3.1, Sections 1 to 3.
