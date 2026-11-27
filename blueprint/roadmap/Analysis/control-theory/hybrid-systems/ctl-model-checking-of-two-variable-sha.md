# CTL model checking of singular hybrid automata with two variables is undecidable

Model checking branching-time temporal logic over singular hybrid automata is undecidable already with two continuous variables, one of which is a clock; with one variable reachability and LTL model checking are decidable.

**Singular hybrid automata.** A singular hybrid automaton has finitely many control modes (some of them initial), finitely many real-valued variables, mode invariants that are polytopes, and transitions between modes, each with a polytope guard and a set of variables reset to $0$; in each mode every variable grows at a constant rational rate fixed by the mode. A run alternates time elapse in a mode, respecting its invariant, with transitions whose guards hold. The reachability problem asks, given a starting valuation and a target polytope, whether some finite run reaches a valuation in the target. Given atomic propositions and a labeling of modes, traces of non-Zeno runs are evaluated against CTL formulas with the standard semantics, and the CTL model-checking problem asks whether all initial modes satisfy a given formula.

**Theorem (Krishna, Mathur and Trivedi).** The CTL model-checking problem for singular hybrid automata with two variables is undecidable.

For singular hybrid automata with one variable, reachability and schedulability are NL-complete and LTL model checking is PSPACE-complete (same source). With three variables, reachability, schedulability, LTL and CTL model checking are undecidable by earlier work of Henzinger, Kopke, Puri and Varaiya and of Asarin, Maler and Pnueli.

## Depends on

- [Hybrid automata and their executions](hybrid-automata-and-their-executions.md)
- [CTL formulas](../../../Logic/temporal-logic/computation-tree-logic/formula.md)
- [Satisfaction of CTL formulas](../../../Logic/temporal-logic/computation-tree-logic/satisfies.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Given a two-counter machine, the proof builds a two-variable singular hybrid automaton and a CTL formula that holds exactly when the machine halts. Both counter values are stored in one variable as $x = 2 - 1/(2^{c_1} 3^{c_2})$; the second variable $y$ has rate $1$ everywhere and is used for bookkeeping, and each instruction becomes a widget whose exit edge has guard $y = 1$ and resets $y$, so every simulated step lets at least one time unit elapse. The branching modalities of CTL check that the widgets updated $x$ correctly.

## Sources

- Shankara Narayanan Krishna, Umang Mathur and Ashutosh Trivedi, "Weak singular hybrid automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2014)*, Lecture Notes in Computer Science 8711, Springer, 2014, pp. 161–175, <https://doi.org/10.1007/978-3-319-10512-3_12>; read as arXiv:1311.3826v3, <https://arxiv.org/abs/1311.3826v3>: the definitions of Section 2, Theorem 1 (the three-variable result, cited from earlier work), Theorem 2 with its proof in the appendix ("Proof of Theorem 2"), and Theorem 3, of that version.
