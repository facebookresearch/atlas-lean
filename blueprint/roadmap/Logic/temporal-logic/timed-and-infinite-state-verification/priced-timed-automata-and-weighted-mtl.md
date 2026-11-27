# Priced timed automata and weighted MTL

A priced timed automaton is a timed automaton whose locations carry cost rates and whose transitions carry cost increments; weighted MTL is LTL whose until operators are constrained by bounds on an accumulated cost, and it is evaluated on finite runs of such automata.

**Priced timed automata.** A priced timed automaton is $\mathcal{A} = (Q, q_0, X, E, \mathrm{Inv}, (\mathrm{cost}_i)_{1 \leq i \leq p})$ with a finite set $Q$ of locations, an initial location $q_0$, a finite set $X$ of clocks, transitions $E \subseteq Q \times \mathcal{C}(X) \times 2^X \times Q$ (guard, clocks to reset, target), invariants $\mathrm{Inv} : Q \to \mathcal{C}(X)$, and cost functions $\mathrm{cost}_i : Q \cup E \to \mathbb{N}$; clock constraints are conjunctions of $x \sim c$ with $c \in \mathbb{N}$ and $\sim\, \in \{<, \leq, =, \geq, >\}$. States are pairs of a location and a clock valuation in $\mathbb{R}_{\geq 0}^X$. A delay of $t$ in location $q$ (respecting the invariant) adds $t \cdot \mathrm{cost}_i(q)$ to cost $i$, and taking a transition $e$ whose guard is true adds $\mathrm{cost}_i(e)$ and resets the chosen clocks. A run is a sequence of delay-then-transition moves, and its $i$-th cost is the sum over its moves. A cost is *stopwatch* if its location rates lie in $\{0, 1\}$. A *labeled* automaton also labels locations with atomic propositions.

**Weighted MTL.** Formulas are $\varphi ::= a \mid \neg\varphi \mid \varphi \vee \varphi \mid \varphi\, U_{\mathrm{cost} \sim c}\, \varphi$ with $a$ an atomic proposition, $\mathrm{cost}$ one of the cost functions, $c \in \mathbb{N}$ and $\sim\, \in \{<, \leq, =, \geq, >\}$. On a finite run $\varrho$, $\varrho \models \varphi_1\, U_{\mathrm{cost} \sim c}\, \varphi_2$ iff some position $0 < \pi \leq |\varrho|$ has $\varrho_{\geq\pi} \models \varphi_2$, every $0 < \pi' < \pi$ has $\varrho_{\geq\pi'} \models \varphi_1$, and the cost of the prefix $\varrho_{\leq\pi}$ satisfies $\sim c$.

**Model checking.** The (existential) model-checking problem asks, given $\mathcal{A}$ and $\varphi$, whether some finite run from the initial state satisfies $\varphi$; since the logic is closed under negation, the results transfer to the universal problem.

## Depends on

- [Clock regions of timed automata](clock-regions-of-timed-automata.md)
- [Timed Büchi automata and timed regular languages](../../../TheoryOfComputation/omega-automata-and-games/timed-automata/timed-buchi-automata.md)
- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

Clocks of the automaton can themselves be used as costs (with rate $1$ everywhere), so weighted MTL subsumes MTL with time-bounded until. The branching-time counterpart WCTL is decidable (PSPACE-complete) on one-clock priced timed automata but undecidable from three clocks on.

## Sources

- P. Bouyer, K. G. Larsen and N. Markey, "Model checking one-clock priced timed automata", *Logical Methods in Computer Science* 4(2), Paper 9, 2008, doi:10.2168/LMCS-4(2:9)2008; read as arXiv:0805.1457v2, <https://arxiv.org/abs/0805.1457v2>: the subsections "Priced Timed Automata" (definition and semantics) and "The Logic WMTL" (syntax, semantics and the model-checking problem).
