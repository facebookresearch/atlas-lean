# Time-bounded reachability of rectangular hybrid automata is undecidable

Reachability of a location within a fixed time bound is undecidable for rectangular hybrid automata whose singular rates may be positive or negative, and for linear hybrid automata with diagonal guards even when every variable has one fixed positive rate; with non-negative rates and no diagonal constraints it is decidable.

**Constraints.** The automata are the [rectangular automata](rectangular-and-initialized-rectangular-automata.md) and linear hybrid automata of the source, with integer rather than rational interval endpoints. Let $\mathcal{I}$ be the set of real intervals with endpoints in $\mathbb{Z} \cup \{\pm\infty\}$. Over a finite set $X$ of real variables, a *rectangular constraint* is $x \in I$ with $I \in \mathcal{I}$, and a *diagonal constraint* is $x - y \sim c$ with $c \in \mathbb{Z}$ and ${\sim} \in \{<, \le, =, \ge, >\}$. Guards are finite conjunctions of such constraints over $X$, rate constraints are conjunctions over the derivatives $\dot{x}$, and update constraints are conjunctions over $X \cup X'$.

**Automata.** A *linear hybrid automaton* (LHA), a special case of [hybrid automata](hybrid-automata-and-their-executions.md), is $\mathcal{H} = (X, L, E, \mathrm{Rate}, \mathrm{Inv}, \ell_{\mathrm{init}})$ with a finite set $L$ of locations, a finite set $E$ of edges $(\ell, g, r, \ell')$ with a guard $g$ and an update $r$, a rate constraint $\mathrm{Rate}(\ell)$ and an invariant (a guard) $\mathrm{Inv}(\ell)$ for each location, and an initial location. A state is $(\ell, \nu)$ with $\nu : X \to \mathbb{R}$; time may elapse by $t \ge 0$ along a rate vector $\dot{\nu}$ satisfying $\mathrm{Rate}(\ell)$ while $\mathrm{Inv}(\ell)$ holds throughout, and an edge may be taken when its guard holds, updating the variables. $\mathcal{H}$ is *rectangular* (an RHA) if all guards, rates and invariants are rectangular (updates assign intervals or keep a variable), *singular* if every rate constraint fixes each $\dot{x}$ to a single value, and *fixed rate* if each variable has the same rate constraint in all locations. The *time-bounded reachability problem* asks, given $\mathcal{H}$, a location $\ell_{\mathrm{goal}}$ and a bound $T \in \mathbb{N}$, whether some finite run from $(\ell_{\mathrm{init}}, \mathbf{0})$ reaches $\ell_{\mathrm{goal}}$ with total duration at most $T$.

**Theorem (Brihaye, Doyen, Geeraerts, Ouaknine, Raskin and Worrell).**

1. The time-bounded reachability problem is undecidable for rectangular hybrid automata, even when restricted to singular rates; the proof uses rates of both signs and time bound $1$ (Theorem 2 of the source).
2. The time-bounded reachability problem is undecidable for linear hybrid automata whose variables all have singular, strictly positive, fixed rates, when diagonal constraints are allowed in guards (Theorem 3).

The same paper shows that time-bounded reachability is decidable for (non-initialized) rectangular hybrid automata with only non-negative rates, a class containing stopwatch automata, for which unbounded reachability is undecidable.

## Depends on

- [Hybrid automata and their executions](hybrid-automata-and-their-executions.md)
- [Rectangular and initialized rectangular automata](rectangular-and-initialized-rectangular-automata.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Both results reduce the halting problem for two-counter machines, which is undecidable. In the first, the steps of the machine are simulated by ticks at times $t_i = 1 - 4^{-i}$, all within one time unit, and a counter with value $v$ after $i$ steps is encoded by a variable with value $4^{-(i+v)}$ at time $t_i$; keeping the encoding up to date requires dividing variables by $4$ between ticks, which divisor gadgets do using rates of both signs. In the second, each counter is written as the difference of two counters that are only incremented, and such a counter with value $v$ is encoded by two variables $x, y$ of rate $1$ with $|x - y| = 2^{-v}$; incrementing halves $|x - y|$ with the help of variables of rates $2$ and $3$, and the diagonal guards compare such differences. In the first construction the goal location is reachable within time $1$ exactly when the machine halts (Theorem 2); in the second, an initialization phase of duration at most $2$ first sets the auxiliary counters to a guessed large value, and the goal is reachable within time $3$ exactly when the machine halts (Theorem 3). A good expansion links a page for the undecidability of halting of two-counter machines started with both counters at $0$, which follows from the linked universality theorem together with the undecidability of halting of Turing machines on the blank tape (the linked halting page states halting for codes on given inputs).

## Sources

- T. Brihaye, L. Doyen, G. Geeraerts, J. Ouaknine, J.-F. Raskin and J. Worrell, "On reachability for hybrid automata over bounded time", in *Automata, Languages and Programming (ICALP 2011)*, Lecture Notes in Computer Science, Springer, 2011, pp. 416–427, doi:10.1007/978-3-642-22012-8_33; read in arXiv:1104.5335v1: the definitions of linear and rectangular hybrid automata and of the time-bounded reachability problem, Theorems 2 and 3 in Section 4 (Undecidability Results) for items 1 and 2, and Theorem 1 in Section 3 for the decidable class with non-negative rates.
