# Plan existence with attention actions is undecidable

Epistemic planning with attention as a bounded resource inherits the undecidability of epistemic planning in dynamic epistemic logic: no algorithm decides whether an attention planning task over arbitrary attention actions has a solution. Restricted to no-free-lunch actions, plan existence becomes decidable.

**Theorem (Belardinelli and Rendsvig).** $\mathsf{PlanEx}$-$\mathcal{T}_{\mathsf{all}}$ is undecidable: no algorithm decides, given an [attention planning task](attention-models-and-attention-planning-tasks.md) $T = (s_0, \Sigma, \varphi_g)$ with $\Sigma$ a finite set of attention actions, whether $T$ has a solution.

The agent set $I$ and the attention bound $N$ are fixed throughout the source; the task (initial attention state, actions and goal) is the input. For the class $\mathsf{nfl}$ of no-free-lunch actions, where $Q^\ast_i = E \times E$ and every question other than $\top$ has positive cost, $\mathsf{PlanEx}$-$\mathcal{T}_{\mathsf{nfl}}$ is decidable (Theorem 25 of the source): along any sequence of applicable actions the updated states eventually stop changing up to bisimulation, so only finitely many plans need checking.

## Depends on

- [Attention models and attention planning tasks](attention-models-and-attention-planning-tasks.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof is a reduction from DEL-based epistemic planning. Bolander, Charrier, Pinchinat and Schwarzentruber show that plan existence for epistemic actions whose preconditions have modal depth at most $n$ and that have no postconditions is undecidable for $n \ge 2$. Every epistemic state has an attention state satisfying the same formulas without attention atoms (Proposition 14 of the source: add any attention resource function), and every epistemic action without postconditions has an equivalent attention action (Proposition 18). So each such epistemic planning task becomes an equivalent attention planning task, computably, and a decision procedure for $\mathsf{PlanEx}$-$\mathcal{T}_{\mathsf{all}}$ would decide the DEL problem.

A good expansion links the undecidability of DEL plan existence with preconditions of modal depth at most $2$ and no postconditions (Bolander, Charrier, Pinchinat and Schwarzentruber, 2020) and the two embedding results (Propositions 14 and 18 of the source); none has a page.

## Sources

- Gaia Belardinelli and Rasmus K. Rendsvig, "Epistemic Planning with Attention as a Bounded Resource", Logic, Rationality, and Interaction (LORI 2021), Lecture Notes in Computer Science 13039, pp. 14–30, Springer, 2021, <https://doi.org/10.1007/978-3-030-88708-7_2>. Read in arXiv:2105.09976v1, <https://arxiv.org/abs/2105.09976v1>; Theorem 24 (undecidability) and its proof, Theorem 25 (decidability for nfl), Definitions 9, 22 and 23, Propositions 14 and 18, numbering of arXiv:2105.09976v1.
- Thomas Bolander, Tristan Charrier, Sophie Pinchinat and François Schwarzentruber, "DEL-based epistemic planning: Decidability and complexity", Artificial Intelligence 287, article 103304, 2020, <https://doi.org/10.1016/j.artint.2020.103304> (the result the proof reduces from, cited by the first source; not read).
