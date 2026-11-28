# ATL with strategy contexts

ATL with strategy contexts (ATLsc) is alternating-time temporal logic in which a strategy chosen by a coalition stays in force, as a context, while nested formulas are evaluated, until it is explicitly revoked.

**Definition.** A *concurrent game structure* (CGS) $\mathcal C = \langle Q, R, \ell, \mathrm{Agt}, M, \mathrm{Mov}, \mathrm{Edge}\rangle$ has a countable set $Q$ of states with a total transition relation $R \subseteq Q^2$ and labelling $\ell : Q \to 2^{AP}$, a finite set $\mathrm{Agt}$ of agents, a nonempty set $M$ of moves, sets $\mathrm{Mov}(q, a) \neq \emptyset$ of moves available to agent $a$ at $q$, and a transition table $\mathrm{Edge}$ giving for each state and each vector of moves (one per agent) an $R$-successor. It is *turn-based* if each state has an owner whose move alone determines the successor. A *strategy* for agent $a$ maps every history (finite path) to a move available at its last state; it is *memoryless* if it depends only on the last state. A strategy $F_A$ for a coalition $A$ assigns a strategy to each member; $F_A \circ F$ updates a context $F$ with $F_A$ (agents of $A$ follow $F_A$, others keep $F$), $F \setminus A$ removes the agents of $A$, and $\mathrm{Out}(\rho, F)$ is the set of infinite continuations of the history $\rho$ consistent with $F$.

*Syntax.* State formulas and path formulas of $\mathrm{ATL}^*_{sc}$ are

$$
\varphi ::= p \mid \neg\varphi \mid \varphi \vee \varphi \mid {\cdot}\rangle A\langle{\cdot}\,\varphi \mid \langle{\cdot} A {\cdot}\rangle\,\psi, \qquad \psi ::= \varphi \mid \neg\psi \mid \psi \vee \psi \mid \mathbf X\psi \mid \psi\,\mathbf U\,\psi,
$$

for $p \in AP$ and coalitions $A \subseteq \mathrm{Agt}$. Under a context $F$: ${\cdot}\rangle A\langle{\cdot}\,\varphi$ holds iff $\varphi$ holds under $F \setminus A$; $\langle{\cdot} A {\cdot}\rangle\,\psi$ holds after a history $\rho$ iff there is a strategy $F_A$ for $A$ such that $\psi$ holds, under the context $F_A \circ F$, along every outcome in $\mathrm{Out}(\rho, F_A \circ F)$; temporal operators are as in LTL. $\mathrm{ATL}_{sc}$ restricts path formulas to $\neg\psi$, $\mathbf X\varphi$ and $\varphi\,\mathbf U\,\varphi$ with state formulas $\varphi$. $\mathrm{ATL}^0_{sc}$ (also written $\mathrm{ATL}_{sc,0}$) is the variant in which $\langle{\cdot} A {\cdot}\rangle$ quantifies over memoryless strategies only. The *satisfiability problem* asks, given a state formula, whether some CGS (with any finite set of agents) has a state satisfying it under the empty context.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

The existential strategy quantifier carries an implicit universal quantification over the outcomes, and so over the strategies of agents outside $A$ that the context leaves free; this is the difference with strategy logic, where every strategy is quantified explicitly. $\mathrm{ATL}_{sc}$ is as expressive as $\mathrm{ATL}^*_{sc}$ (Brihaye, Da Costa, Laroussinie and Markey). Satisfiability of $\mathrm{ATL}_{sc}$ over concurrent games is undecidable (Troquard and Walther), but becomes decidable over turn-based games and when the number of moves is bounded, through a translation into quantified CTL under the tree semantics.

## Sources

- F. Laroussinie and N. Markey, "Satisfiability of ATL with strategy contexts", in *Proceedings of the Fourth International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2013)*, Electronic Proceedings in Theoretical Computer Science 119, 2013, pp. 208–223, <https://doi.org/10.4204/EPTCS.119.18>; numbers from arXiv:1307.4478v1, <https://arxiv.org/abs/1307.4478v1>: Definitions 1 to 3, Theorem 10 and the algorithm after it (turn-based satisfiability is decidable through QCTL* under the tree semantics), Theorem 11 (its non-elementary lower bound), and Theorem 12 with Corollary 13 (bounded moves).
