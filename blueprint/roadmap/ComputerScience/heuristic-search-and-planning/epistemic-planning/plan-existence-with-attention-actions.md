# Plan existence with attention actions is undecidable, already for actions with trivial questions

Epistemic planning with attention as a bounded resource inherits the undecidability of epistemic planning in dynamic epistemic logic: for two or more agents, no algorithm decides whether an attention planning task has a solution, already when every action asks only the trivial question.

**Theorem (Belardinelli and Rendsvig).** For every fixed agent set $I$ with at least two agents, $\mathsf{PlanEx}$-$\mathcal{T}_{\mathsf{triv}}$ is undecidable: no algorithm decides, given an [attention planning task](attention-models-and-attention-planning-tasks.md) $T = (s_0, \Sigma, \varphi_g)$ with $\Sigma$ a finite set of attention actions with trivial questions, whether $T$ has a solution (Theorem 24 of the source, whose proof produces only such actions, by Proposition 18).

The agent set $I$ and the attention bound $N$ are fixed throughout the source; the task (initial attention state, actions and goal) is the input. The source's proof transfers the undecidability of DEL plan existence without postconditions, which holds for two or more agents and fails for one, where that problem is decidable (Section 5 of the source); so the theorem is stated for $|I| \ge 2$. The source states Theorem 24 for the class $\mathsf{all}$ of all attention actions, but its update (Definition 8) can leave the attention states, on which it is defined, so iterated updates by general attention actions are not settled by the source; the trivial-question actions of its proof keep every reached state an attention state. For the same reason the source's decidability result for no-free-lunch actions (Theorem 25), whose updates use the question filter, is not stated here.

## Depends on

- [Attention models and attention planning tasks](attention-models-and-attention-planning-tasks.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof is a reduction from DEL-based epistemic planning. Bolander, Charrier, Pinchinat and Schwarzentruber show that plan existence for epistemic actions whose preconditions have modal depth at most $n$ and that have no postconditions is undecidable for $n \ge 2$. Every epistemic state has an attention state satisfying the same formulas without attention atoms (Proposition 14 of the source: add any attention resource function), and every epistemic action without postconditions has an equivalent attention action with trivial questions: the same events, relations and preconditions, every question $\top$ and $Q^\ast_i$ the identity (Proposition 18). Its update is the product update of the epistemic action. So each such epistemic planning task becomes an equivalent task in $\mathcal{T}_{\mathsf{triv}}$, computably, and a decision procedure for $\mathsf{PlanEx}$-$\mathcal{T}_{\mathsf{triv}}$ would decide the DEL problem.

A good expansion links the undecidability of DEL plan existence with preconditions of modal depth at most $2$ and no postconditions (Bolander, Charrier, Pinchinat and Schwarzentruber, 2020) and the two embedding results (Propositions 14 and 18 of the source).

## Sources

- Gaia Belardinelli and Rasmus K. Rendsvig, "Epistemic Planning with Attention as a Bounded Resource", Logic, Rationality, and Interaction (LORI 2021), Lecture Notes in Computer Science 13039, pp. 14–30, Springer, 2021, <https://doi.org/10.1007/978-3-030-88708-7_2>. Read in arXiv:2105.09976v1, <https://arxiv.org/abs/2105.09976v1>; Theorem 24 (undecidability) and its proof, Theorem 25 (decidability for nfl), Definitions 9, 22 and 23, Propositions 14 and 18, numbering of arXiv:2105.09976v1.
