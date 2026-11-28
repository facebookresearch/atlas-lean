# Difference HS over traces with constraints for A, L or O is Σ¹₁-hard

Adding to the interval temporal logic HS over the traces of a finite Kripke structure a constraint on the difference between the length of the next interval and the current one makes satisfiability $\Sigma^1_1$-hard as soon as one of the Allen relations A, L, O or their inverses is constrained.

**Setting.** Over a linear order, an interval is $[x, y]$ with $x \le y$ (point intervals included), and the source's Allen relations (Table 1) are: $[x,y]\,A\,[v,z]$ iff $y = v$ (meets); $L$ iff $y < v$ (before); $B$ iff $x = v$ and $z < y$ (started-by); $E$ iff $y = z$ and $x < v$ (finished-by); $D$ iff $x < v$ and $z < y$ (contains); $O$ iff $x < v < y < z$ (overlaps); and $\overline{X}$ is the inverse of $X$. Halpern and Shoham's logic HS has an existential modality $\langle X\rangle$ for each $X \in \{A, L, B, E, D, O, \overline{A}, \overline{L}, \overline{B}, \overline{E}, \overline{D}, \overline{O}\}$. Under the trace-based semantics, formulas are evaluated on the finite intervals of the infinite paths (traces) of a finite [Kripke structure](../temporal-specification/kripke-structures-with-initial-states.md), with a homogeneous valuation (a proposition holds on an interval when it holds at all its positions). *Difference HS* (DHS) adds, for every relation $X$, constrained modalities $\langle X\rangle_{\Delta \sim c}$ with $\sim \in \{<, \le, =, >, \ge\}$ and $c \in \mathbb{Z}$ given in binary: $I \models \langle X\rangle_{\Delta \sim c}\varphi$ if some interval $J$ with $I\, X\, J$ and $|J| - |I| \sim c$ satisfies $\varphi$, where $|[i, j]| = j - i + 1$. $\mathrm{DHS}_X$ is the fragment with constrained modalities for the relation $X$ only. For a finite set $\mathrm{AP}$ of propositions, a trace $w$ (an infinite word over $2^{\mathrm{AP}}$) satisfies $\varphi$ if $\varphi$ holds at its initial interval $[0, 0]$. Model checking asks, for a finite Kripke structure $K$ with a left-total transition relation and an initial state, and a formula $\varphi$, whether every trace of an infinite path of $K$ from its initial state satisfies $\varphi$; satisfiability asks whether some trace over $\mathrm{AP}$ satisfies $\varphi$.

**Theorem (Bozzelli and Peron).** For each $X \in \{A, L, O, \overline{A}, \overline{L}, \overline{O}\}$, satisfiability for $\mathrm{DHS}_X$ is $\Sigma^1_1$-hard, even if the only constant used in the constraints is $0$; for $X \in \{A, O, \overline{A}, \overline{O}\}$ this holds even if the only constraint used is $\ge 0$ (or, dually, $\le 0$) (Theorem 4.1 of the source, whose reduction maps recurrence to satisfiability).

Theorem 4.1 also states $\Sigma^1_1$-hardness for model checking. Model checking as defined here is universal: a no-instance has an existential witness (an infinite path and the truth values of the subformulas at all intervals, subject to arithmetical conditions), so the problem lies in $\Pi^1_1$ and is not $\Sigma^1_1$-hard under many-one reductions. What the satisfiability reduction gives for model checking, through the Kripke structure whose traces are all words over $\mathrm{AP}$ and the negated formula, is $\Sigma^1_1$-hardness of its complement.

By contrast, the fragment that allows constrained modalities only for $B$, $D$, $E$ and their inverses is decidable, and the source shows that its model checking and satisfiability are at least 2EXPSPACE-hard (Theorem 5.5).

## Depends on

- [Kripke structures with initial states](../temporal-specification/kripke-structures-with-initial-states.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The proof gives polynomial-time reductions from the recurrence problem for non-deterministic Minsky two-counter machines: does some infinite computation from a designated initial transition take a designated recurrent transition infinitely often? Computations are encoded along a trace, and constrained modalities with constant $0$ compare interval lengths so that consecutive configurations respect the increments, decrements and zero tests. The recurrence problem is $\Sigma^1_1$-complete (Harel). A good expansion links pages for the analytical hierarchy, its level $\Sigma^1_1$ and the reductions that define hardness for it, which the statement uses.

## Sources

- Laura Bozzelli and Adriano Peron, "A quantitative extension of interval temporal logic over infinite words", in *29th International Symposium on Temporal Representation and Reasoning (TIME 2022)*, LIPIcs 247, 11:1–11:16, 2022, doi:[10.4230/LIPIcs.TIME.2022.11](https://doi.org/10.4230/LIPIcs.TIME.2022.11). Numbering of the version read, arXiv:2206.13920v2: Section 3 (difference interval temporal logic), Theorem 4.1 and Lemma 4.2 in Section 4, and Theorem 5.5.
