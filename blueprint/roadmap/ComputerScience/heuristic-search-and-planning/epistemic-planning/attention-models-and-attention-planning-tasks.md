# Attention models and attention planning tasks

Attention models are epistemic Kripke models in which each agent has a bounded attention resource. Attention actions are event models with a question for each agent and a cost function: an agent who can afford the cost of its question learns its answer, and planning asks for a sequence of such actions reaching an epistemic goal.

**Language (Belardinelli and Rendsvig).** Fix a finite nonempty set $I$ of agents and an attention bound $N \in \mathbb{N}$. Let $\Phi$ be a countable set of proposition atoms and $\Psi = \{(\alpha_i < n), (\alpha_i = n) : n \le N, i \in I\}$ a set of attention atoms, with $At = \Phi \uplus \Psi$. The language $\mathcal{L}$ is $\varphi ::= \top \mid p \mid \neg\varphi \mid \varphi \wedge \varphi \mid K_i \varphi$ with $p \in At$ and $i \in I$.

**Attention states.** An *attention model* is $M = (W, R, V, A)$ with a nonempty finite set $W$ of worlds, an equivalence relation $R_i$ on $W$ for each $i \in I$, a valuation $V : At \to \mathcal{P}(W)$ and an attention resource function $A : I \times W \to \{0, \dots, N\}$ with $A_i(w) = A_i(v)$ whenever $w R_i v$. A pair $(M, w)$ with $w \in W$ is an *attention state*. Satisfaction is as in epistemic logic, with $M, w \models (\alpha_i = n)$ iff $A_i(w) = n$ and $M, w \models (\alpha_i < n)$ iff $A_i(w) < n$.

**Attention actions.** An *attention action model* is $\mathcal{A} = (E, Q, Q^\ast, \mathrm{pre}, c)$ with a nonempty finite set $E$ of events, equivalence relations $Q_i$ and $Q^\ast_i$ on $E$ for each agent, preconditions $\mathrm{pre} : E \to \mathcal{L}$, and a cost function $c : I \times \mathcal{L} \times E \to \mathbb{N}$ with $c_i(\top, e) = 0$ and $c_i(\varphi, e) = c_i(\varphi, e')$ whenever $(e, e') \in Q_i \cup Q^\ast_i$. A *question map* assigns each agent $i$ a formula $\mathsf{q}_i$. An *attention action* is a triple $X = (\mathcal{A}, \mathsf{q}, e)$ with an actual event $e$; $\mathsf{all}$ is the class of all attention actions. There are no postconditions. Since the update below reads the cost function only at the questions, an attention action is a finite object for algorithmic purposes: the events, the relations $Q_i, Q^\ast_i$, the preconditions, the questions $\mathsf{q}_i$ and the finitely many values $c_i(\mathsf{q}_i, e)$; an attention state is given by its finite model with the valuation restricted to the finitely many atoms the task mentions.

**Update.** For a formula $\varphi$ let $Q^\ast_i[\varphi \mid \neg\varphi]$ be $Q^\ast_i$ minus the pairs $(e, e')$ with $\mathrm{pre}(e) \models \varphi$ and $\mathrm{pre}(e') \not\models \varphi$. The update $(M, w) \otimes X$ has worlds $W^X = \{(w, e) \mid M, w \models \mathrm{pre}(e)\}$, actual world $(w, e)$, valuation of $p \in \Phi$ inherited from $w$, resources $A^X_i(w, e) = \max\{0, A_i(w) - c_i(\mathsf{q}_i, e)\}$, and $(w, e) R^X_i (v, f)$ iff $w R_i v$ and $(e, f)$ belongs to $Q_i \cup Q^\ast_i$ if $c_i(\mathsf{q}_i, e) > A_i(w)$, and to $Q_i \cup Q^\ast_i[\mathsf{q}_i \mid \neg\mathsf{q}_i]$ if $c_i(\mathsf{q}_i, e) \le A_i(w)$. Definition 8 of the source writes the second case as $c_i(\mathsf{q}_i, e) \le A_i(w) \ne 0$, which leaves the case $c_i(\mathsf{q}_i, e) = A_i(w) = 0$ without a clause; it is filled here by the second case, which is what the emulation of epistemic actions in Proposition 18 of the source needs (there every agent asks $\top$ at cost $0$). An action is *applicable* to $(M, w)$ if $M, w \models \mathrm{pre}(e)$.

**Planning.** An *attention planning task* $T = (s_0, \Sigma, \varphi_g)$ consists of an initial attention state $s_0$, a finite set $\Sigma$ of attention actions and a goal $\varphi_g \in \mathcal{L}$. A *solution* is a finite sequence $X_1, \dots, X_n$ of actions from $\Sigma$, each applicable to the result of the previous ones, with $s_0 \otimes X_1 \otimes \cdots \otimes X_n \models \varphi_g$. For a class $\mathsf{X}$ of attention actions, $\mathsf{PlanEx}$-$\mathcal{T}_{\mathsf{X}}$ asks, given a task with $\Sigma \subseteq \mathsf{X}$, whether it has a solution.

## Depends on

- [A Kripke model as a first-order structure](../../../Logic/modal-logic/standard-translation-of-modal-logic/kripke-structure.md)
- [Action model logic](../../../Logic/modal-logic/action-model-logic.md)

## Proof depends on

None.

## Expansion

$Q_i$ is unavoidable indistinguishability of events, $Q^\ast_i$ default indistinguishability that attention can break. Attention states embed into epistemic states (Proposition 13 of the source) and conversely for formulas without attention atoms (Proposition 14); every action model without postconditions has an equivalent attention action (Proposition 18). The class $\mathsf{nfl}$ (no free lunch) requires $Q^\ast_i = E \times E$ and $c_i(\varphi, e) > 0$ for every $\varphi \ne \top$.

## Sources

- Gaia Belardinelli and Rasmus K. Rendsvig, "Epistemic Planning with Attention as a Bounded Resource", Logic, Rationality, and Interaction (LORI 2021), Lecture Notes in Computer Science 13039, pp. 14–30, Springer, 2021, <https://doi.org/10.1007/978-3-030-88708-7_2>. Read in arXiv:2105.09976v1, <https://arxiv.org/abs/2105.09976v1>; Section 2.1, Definitions 1, 2, 7, 8, 9, 22 and 23, Propositions 13, 14 and 18, numbering of arXiv:2105.09976v1.
