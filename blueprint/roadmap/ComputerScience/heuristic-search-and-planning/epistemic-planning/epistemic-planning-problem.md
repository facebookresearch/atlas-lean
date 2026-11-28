# The epistemic planning problem

The epistemic planning problem asks, given a pointed multi-agent Kripke model, a finite set of event models and an epistemic goal formula, whether some finite sequence of actions, applied by product update, leads to a model satisfying the goal.

Fix a finite set $Ag$ of agents and a countable set $AP$ of propositions.

**Language.** $\mathcal{L}_{EL}$ is given by $\varphi ::= \top \mid p \mid \neg\varphi \mid (\varphi \vee \varphi) \mid K_a \varphi \mid C_G \varphi$ with $p \in AP$, $a \in Ag$, $G \subseteq Ag$; $\hat{C}_G \varphi$ abbreviates $\neg C_G \neg \varphi$.

**States.** A state is $S = (W, (R_a)_{a \in Ag}, V, w_0)$ with a nonempty set $W$ of worlds, equivalence relations $R_a$ on $W$ (S5), a valuation $V \colon W \to 2^{AP}$ and an actual world $w_0$. $K_a \varphi$ holds at $w$ if $\varphi$ holds at every $w'$ with $w R_a w'$, and $C_G \varphi$ if $\varphi$ holds at every $w'$ reachable from $w$ by the reflexive transitive closure of $\bigcup_{a \in G} R_a$.

**Actions.** An action is $A = (E, (R_a)_{a \in Ag}, \mathit{pre}, \mathit{post}, e_0)$ with a nonempty finite set $E$ of events, equivalence relations $R_a$ on $E$, preconditions $\mathit{pre} \colon E \to \mathcal{L}_{EL}$, postconditions $\mathit{post} \colon E \times AP \to \mathcal{L}_{EL}$ and an actual event $e_0$; it is public if $|E| = 1$.

**Product.** If $S \models \mathit{pre}(e_0)$, then $S \otimes A = (W', (R'_a), V', (w_0, e_0))$ with $W' = \{(w, e) \in W \times E \mid (S, w) \models \mathit{pre}(e)\}$, $(w, e) R'_a (w', e')$ iff $w R_a w'$ and $e R_a e'$, and $V'((w, e)) = \{p \mid (S, w) \models \mathit{post}(e, p)\}$; otherwise the product is undefined.

**Problem.** Input: a state $S$, a finite set $\mathcal{A}$ of actions and a formula $\varphi \in \mathcal{L}_{EL}$. A finite state is given by listing its worlds, the pairs of each $R_a$, the actual world and the valuation of the finitely many propositions that occur in the input, all other propositions being false everywhere; an action is given likewise, with its preconditions and postconditions as formulas. An infinite state can be an input only through a finite presentation, such as the automatic presentations of [epistemic planning over automatic models](epistemic-planning-over-automatic-models.md). Question: is there a sequence $A_1, \dots, A_m \in \mathcal{A}$ such that $S \otimes A_1 \otimes \cdots \otimes A_m$ is defined and satisfies $\varphi$?

## Depends on

- [Epistemic models](../../../Logic/modal-logic/epistemic-logic/model.md)
- [Action model logic](../../../Logic/modal-logic/action-model-logic.md)

## Proof depends on

None.

## Expansion

Actions are the pointed event models of Baltag, Moss and Solecki, and the problem is that of Bolander and Andersen. Classical planning is the case of a single world and public actions; public actions over finite initial states give a decidable problem (Kominis and Geffner). When the initial state is infinite it is given by an automatic presentation, its worlds and relations being recognized by finite automata.

## Sources

- Sébastien Lê Cong, Sophie Pinchinat and François Schwarzentruber, "Small undecidable problems in epistemic planning", *Proceedings of the Twenty-Seventh International Joint Conference on Artificial Intelligence (IJCAI 2018)*, 4780–4786, 2018, <https://doi.org/10.24963/ijcai.2018/664>; read as the open-access proceedings version, <https://www.ijcai.org/proceedings/2018/0664.pdf>: Definitions 1 (states), 2 (actions), 3 (product) and 4 (epistemic planning problem) in Section 2.
- Filippos Kominis and Hector Geffner, "Beliefs in multiagent planning: from one agent to many", *Proceedings of the Twenty-Fifth International Conference on Automated Planning and Scheduling (ICAPS 2015)*, 147–155, 2015, <https://doi.org/10.1609/icaps.v25i1.13726>: decidability of planning with public actions over finite states, as recalled in Section 1 of the IJCAI paper above.
