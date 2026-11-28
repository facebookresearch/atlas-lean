# Priced timed automata

A priced timed automaton is a timed automaton whose locations carry cost rates and whose transitions carry cost increments, so that every run accumulates one or more costs alongside its clock values.

A priced timed automaton is $\mathcal{A} = (Q, q_0, X, E, \mathrm{Inv}, (\mathrm{cost}_i)_{1 \leq i \leq p})$ with a finite set $Q$ of locations, an initial location $q_0$, a finite set $X$ of clocks, transitions $E \subseteq Q \times \mathcal{C}(X) \times 2^X \times Q$ (guard, clocks to reset, target), invariants $\mathrm{Inv} : Q \to \mathcal{C}(X)$, and cost functions $\mathrm{cost}_i : Q \cup E \to \mathbb{N}$; clock constraints are conjunctions of $x \sim c$ with $c \in \mathbb{N}$ and $\sim\, \in \{<, \leq, =, \geq, >\}$. States are pairs of a location and a clock valuation in $\mathbb{R}_{\geq 0}^X$. A delay of $t$ in location $q$ (respecting the invariant) adds $t \cdot \mathrm{cost}_i(q)$ to cost $i$, and taking a transition $e$ whose guard is true adds $\mathrm{cost}_i(e)$ and resets the chosen clocks. A run is a sequence of delay-then-transition moves, and its $i$-th cost is the sum over its moves. A cost is *stopwatch* if its location rates lie in $\{0, 1\}$. A *labeled* automaton also labels locations with atomic propositions.

## Depends on

- [Clock regions of timed automata](clock-regions-of-timed-automata.md)
- [Timed Büchi automata and timed regular languages](../../../TheoryOfComputation/omega-automata-and-games/timed-automata/timed-buchi-automata.md)

## Proof depends on

None.

## Expansion

Clocks of the automaton can themselves be used as costs (with rate $1$ everywhere). Costs only observe runs: guards and invariants never test them.

## Sources

- P. Bouyer, K. G. Larsen and N. Markey, "Model checking one-clock priced timed automata", *Logical Methods in Computer Science* 4(2), Paper 9, 2008, doi:10.2168/LMCS-4(2:9)2008; read as arXiv:0805.1457v2, <https://arxiv.org/abs/0805.1457v2>: Section 1.1, Definition 1.1 and Remark 1.2 of arXiv:0805.1457v2.
