# Reachability for constant-rate multi-mode systems with one added clock is undecidable

Constant-rate multi-mode systems, whose modes may be switched freely inside a safety set, have polynomial-time reachability, but adding a single clock that may be tested and reset makes reachability undecidable already with three rate variables.

**Singular hybrid automata.** A singular hybrid automaton has finitely many control modes (some of them initial), finitely many real-valued variables, mode invariants that are polytopes, and transitions between modes, each with a polytope guard and a set of variables reset to $0$; in each mode every variable grows at a constant rational rate fixed by the mode. A run alternates time elapse in a mode, respecting its invariant, with transitions whose guards hold. The reachability problem asks, given a starting valuation and a target polytope, whether some finite run reaches a valuation in the target.

**Constant-rate multi-mode systems.** A constant-rate multi-mode system (CMS) is a singular hybrid automaton with a bounded open polytope $S$, the safety set, that is the invariant of every mode, whose modes form one strongly connected component, and whose transitions all have guard $\top$ and reset no variable. Reachability and schedulability for CMS are decidable in polynomial time (Alur, Trivedi and Wojtczak).

**Theorem (Krishna, Mathur and Trivedi).** The reachability problem is undecidable for constant-rate multi-mode systems with three variables extended by one unrestricted clock, that is, one further variable of rate $1$ in every mode that transitions may test in guards and reset.

In the source's construction the guards and resets involve only the clock. The same section also states that reachability is undecidable for three-variable weak singular hybrid automata (layered compositions of CMS) extended with discrete updates of the variables (Theorem 7), whereas reachability for weak singular hybrid automata themselves is NP-complete (Theorem 5); the clock of the theorem above is the source's way of allowing such updates inside a strongly connected component.

## Depends on

- [Hybrid automata and their executions](hybrid-automata-and-their-executions.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof simulates a two-counter machine: the rate variables $x_1, x_2$ store the counters as $x_i = 5 - 2^{-c_i}$, a third variable $y$ is returned to $1$ at the start of each widget, and the clock $x$, reset on every transition and tested in guards (against $0$ and $1$), together with the invariants fixes the time spent in each mode, so that the constant rates move $x_1$, $x_2$ and $y$ by prescribed amounts. Increment, decrement and zero-test widgets are connected according to the machine's program, and the mode for the halting instruction is reachable exactly when the machine halts.

## Sources

- Shankara Narayanan Krishna, Umang Mathur and Ashutosh Trivedi, "Weak singular hybrid automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2014)*, Lecture Notes in Computer Science 8711, Springer, 2014, pp. 161–175, <https://doi.org/10.1007/978-3-319-10512-3_12>; read as arXiv:1311.3826v3, <https://arxiv.org/abs/1311.3826v3>: the definition of constant-rate multi-mode systems and Theorem 4 in Section 3, the definition of weak singular hybrid automata and Theorem 5, and Theorems 7 and 8 of Section 4 ("Undecidable variants of WSHA") with the proof of Theorem 8 in the appendix, of that version.
- Rajeev Alur, Ashutosh Trivedi and Dominik Wojtczak, "Optimal scheduling for constant-rate multi-mode systems", in *Hybrid Systems: Computation and Control (HSCC 2012)*, ACM, 2012, pp. 75–84, <https://doi.org/10.1145/2185632.2185647> (cited after the paper above, for the polynomial-time result).
