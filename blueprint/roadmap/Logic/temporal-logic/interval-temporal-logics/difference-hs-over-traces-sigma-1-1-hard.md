# Difference HS over traces with constraints for A, L or O is Σ¹₁-hard

Adding to the interval temporal logic HS over the traces of a finite Kripke structure a constraint on the difference between the length of the next interval and the current one makes model checking and satisfiability $\Sigma^1_1$-hard as soon as one of the Allen relations A, L, O or their inverses is constrained.

**Setting.** Halpern and Shoham's logic HS has an existential modality $\langle X\rangle$ for each of [Allen's interval relations](horn-fragments-of-the-halpern-shoham-logic.md) $X \in \{A, L, B, E, D, O, \overline{A}, \overline{L}, \overline{B}, \overline{E}, \overline{D}, \overline{O}\}$. Under the trace-based semantics, formulas are evaluated on the finite intervals of the infinite paths (traces) of a finite [Kripke structure](../temporal-specification/kripke-structures-with-initial-states.md), with a homogeneous valuation (a proposition holds on an interval when it holds at all its positions). *Difference HS* (DHS) adds, for every relation $X$, constrained modalities $\langle X\rangle_{\Delta \sim c}$ with $\sim \in \{<, \le, =, >, \ge\}$ and $c \in \mathbb{Z}$ given in binary: $I \models \langle X\rangle_{\Delta \sim c}\varphi$ if some interval $J$ with $I\, X\, J$ and $|J| - |I| \sim c$ satisfies $\varphi$. $\mathrm{DHS}_X$ is the fragment with constrained modalities for the relation $X$ only. Model checking asks whether a given finite Kripke structure satisfies a given formula under this semantics, and satisfiability whether some trace satisfies it.

**Theorem (Bozzelli and Peron).** For each $X \in \{A, L, O, \overline{A}, \overline{L}, \overline{O}\}$, model checking and satisfiability for $\mathrm{DHS}_X$ are $\Sigma^1_1$-hard, even if the only constant used in the constraints is $0$; for $X \in \{A, O, \overline{A}, \overline{O}\}$ this holds even if the only constraint used is $\ge 0$ (or, dually, $\le 0$) (Theorem 4.1 of the source).

By contrast, the fragment that allows constrained modalities only for $B$, $D$, $E$ and their inverses is decidable, and the source shows that its model checking and satisfiability are at least 2EXPSPACE-hard (Theorem 5.5).

## Depends on

- [Horn fragments of the Halpern–Shoham logic](horn-fragments-of-the-halpern-shoham-logic.md)
- [Kripke structures with initial states](../temporal-specification/kripke-structures-with-initial-states.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The proof gives polynomial-time reductions from the recurrence problem for non-deterministic Minsky two-counter machines: does some infinite computation from a designated initial transition take a designated recurrent transition infinitely often? Computations are encoded along a trace, and constrained modalities with constant $0$ compare interval lengths so that consecutive configurations respect the increments, decrements and zero tests. The recurrence problem is $\Sigma^1_1$-complete (Harel).

## Sources

- Laura Bozzelli and Adriano Peron, "A quantitative extension of interval temporal logic over infinite words", in *29th International Symposium on Temporal Representation and Reasoning (TIME 2022)*, LIPIcs 247, 11:1–11:16, 2022, doi:[10.4230/LIPIcs.TIME.2022.11](https://doi.org/10.4230/LIPIcs.TIME.2022.11). Numbering of the version read, arXiv:2206.13920v2: Section 3 (difference interval temporal logic), Theorem 4.1 and Lemma 4.2 in Section 4, and Theorem 5.5.
