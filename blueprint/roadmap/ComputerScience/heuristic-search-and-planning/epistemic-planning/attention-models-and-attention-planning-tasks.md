# Attention models and attention planning tasks

Attention models are epistemic Kripke models in which each agent has a bounded attention resource. Attention actions are event models with a question for each agent and a cost function: an agent who can afford the cost of its question can learn its answer, except between events it cannot distinguish anyway. Planning asks for a sequence of actions reaching an epistemic goal; it is stated here for the actions with trivial questions, under which updates stay within attention states.

**Language (Belardinelli and Rendsvig).** Fix a finite nonempty set $I$ of agents and an attention bound $N \in \mathbb{N}$. Let $\Phi$ be a countable set of proposition atoms and $\Psi = \{(\alpha_i < n), (\alpha_i = n) : n \le N, i \in I\}$ a set of attention atoms, with $At = \Phi \uplus \Psi$. The language $\mathcal{L}$ is $\varphi ::= \top \mid p \mid \neg\varphi \mid \varphi \wedge \varphi \mid K_i \varphi$ with $p \in At$ and $i \in I$.

**Attention states.** An *attention model* is $M = (W, R, V, A)$ with a nonempty finite set $W$ of worlds, an equivalence relation $R_i$ on $W$ for each $i \in I$, a valuation $V : At \to \mathcal{P}(W)$ and an attention resource function $A : I \times W \to \{0, \dots, N\}$ with $A_i(w) = A_i(v)$ whenever $w R_i v$. A pair $(M, w)$ with $w \in W$ is an *attention state*. Satisfaction is as in epistemic logic, with $M, w \models K_i\varphi$ iff $\varphi$ holds at every $R_i$-successor of $w$, with $M, w \models (\alpha_i = n)$ iff $A_i(w) = n$ and $M, w \models (\alpha_i < n)$ iff $A_i(w) < n$.

**Attention actions.** An *attention action model* is $\mathcal{A} = (E, Q, Q^\ast, \mathrm{pre}, c)$ with a nonempty finite set $E$ of events, equivalence relations $Q_i$ and $Q^\ast_i$ on $E$ for each agent, preconditions $\mathrm{pre} : E \to \mathcal{L}$, and a cost function $c : I \times \mathcal{L} \times E \to \mathbb{N}$ with $c_i(\top, e) = 0$ and $c_i(\varphi, e) = c_i(\varphi, e')$ whenever $(e, e') \in Q_i \cup Q^\ast_i$. A *question map* assigns each agent $i$ a formula $\mathsf{q}_i$. An *attention action* is a triple $X = (\mathcal{A}, \mathsf{q}, e)$ with an actual event $e$; $\mathsf{all}$ is the class of all attention actions. There are no postconditions. The class $\mathsf{triv}$ of attention actions *with trivial questions* consists of those with $\mathsf{q}_i = \top$ and $Q^\ast_i$ the identity on $E$ for every agent: these are the actions built in the proof of Proposition 18 of the source, which emulate the epistemic actions without postconditions. Such an action is a finite object: the events, the relations $Q_i$ and the preconditions.

**Update.** Definition 8 of the source updates an attention state $(M, w)$ with an attention action $X$: the worlds are $W^X = \{(w, e) \mid M, w \models \mathrm{pre}(e)\}$, the actual world is $(w, e)$, the valuation of $p \in \Phi$ is inherited from $w$, the resources are $A^X_i(w, e) = \max\{0, A_i(w) - c_i(\mathsf{q}_i, e)\}$, and $(w, e) R^X_i (v, f)$ requires $w R_i v$ and that $(e, f)$ belong to $Q_i \cup Q^\ast_i$, from which the pairs $(e, e')$ with $\mathrm{pre}(e) \models \mathsf{q}_i$ and $\mathrm{pre}(e') \not\models \mathsf{q}_i$ are removed when agent $i$ can afford its question. For an action in $\mathsf{triv}$ the question $\top$ is free and removes no pair, so the update is $(w, e) R^X_i (v, f)$ iff $w R_i v$ and $e \,Q_i\, f$, with $A^X = A$: the product update with the equivalences $Q_i$, which is again an attention state. An action is *applicable* to $(M, w)$ if $M, w \models \mathrm{pre}(e)$.

For general attention actions the update of an attention state need not be an attention state. For one agent, a world $w$ with $p$ true and $A_i(w) = 1$, events $e, f$ with $\mathrm{pre}(e) = p$ and $\mathrm{pre}(f) = \top$, $Q_i$ the identity, $Q^\ast_i = \{e, f\}^2$ and the question $p$ at cost $0$, the filter removes $(e, f)$ but keeps $(f, e)$, so $R^X_i$ is not symmetric. The source does not say how a second update, or the entailment $\mathrm{pre}(e) \models \mathsf{q}_i$, is to be read on such models, so planning is stated here only for $\mathsf{triv}$.

**Planning.** An *attention planning task* $T = (s_0, \Sigma, \varphi_g)$ consists of an initial attention state $s_0$, a finite set $\Sigma$ of attention actions and a goal $\varphi_g \in \mathcal{L}$. A *solution* is a finite sequence $X_1, \dots, X_n$ of actions from $\Sigma$, each applicable to the result of the previous ones, with $s_0 \otimes X_1 \otimes \cdots \otimes X_n \models \varphi_g$ (Definition 22). For $\Sigma \subseteq \mathsf{triv}$ every state reached is an attention state, and $\mathsf{PlanEx}$-$\mathcal{T}_{\mathsf{triv}}$ asks, given a task with $\Sigma \subseteq \mathsf{triv}$, whether it has a solution (Definition 23).

$Q_i$ is unavoidable indistinguishability of events, $Q^\ast_i$ default indistinguishability that attention can break. Attention states embed into epistemic states (Proposition 13 of the source) and conversely for formulas without attention atoms (Proposition 14). The class $\mathsf{nfl}$ (no free lunch) of the source requires $Q^\ast_i = E \times E$ and $c_i(\varphi, e) > 0$ for every $\varphi \ne \top$; its updates use the question filter.

## Depends on

- [Epistemic models](../../../Logic/modal-logic/epistemic-logic/model.md)
- [Action model logic](../../../Logic/modal-logic/action-model-logic.md)

## Proof depends on

None.

## Sources

- Gaia Belardinelli and Rasmus K. Rendsvig, "Epistemic Planning with Attention as a Bounded Resource", Logic, Rationality, and Interaction (LORI 2021), Lecture Notes in Computer Science 13039, pp. 14–30, Springer, 2021, <https://doi.org/10.1007/978-3-030-88708-7_2>. Read in arXiv:2105.09976v1, <https://arxiv.org/abs/2105.09976v1>; Section 2.1, Definitions 1, 2, 7, 8, 9, 22 and 23, Propositions 13, 14 and 18, numbering of arXiv:2105.09976v1.
