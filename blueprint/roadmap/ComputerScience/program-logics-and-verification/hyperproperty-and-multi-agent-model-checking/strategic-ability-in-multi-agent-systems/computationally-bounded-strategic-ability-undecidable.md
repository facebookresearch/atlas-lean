# Model checking computationally bounded strategic ability is undecidable

When strategies of agents in imperfect-information concurrent games are required to be Turing machines of bounded time complexity, deciding whether a coalition has such a strategy for a temporal objective is undecidable: already for one agent and a safety objective over a computable family of games, and for two agents over a single game.

**Setting (Dima and Jamroga).** An imperfect-information concurrent game structure (iCGS) has finitely many states with an initial state, agents with indistinguishability relations on states, each an equivalence relation whose classes are the observations strategies read, actions available to each agent in each state, required to be uniform ($q \sim_a q'$ implies that agent $a$ has the same actions at $q$ and $q'$; Definition 2.1), a deterministic transition function on joint actions, and a labeling by atomic propositions. A *model template* is a countable family $\mathcal{M} = (M_1, M_2, \dots)$ of finite iCGSs over the same agents, actions and propositions. A *general computational strategy* for an agent is a deterministic, total Turing machine that receives the representation of a model and a sequence of the agent's observations and outputs one of its actions; a coalition's strategy is one such machine per member, and its time complexity is the maximum of the members' running times as a function of the model's encoding size and the input length. A coalition $A$ has *uniform $\mathcal{C}$-ability* in $\mathcal{M}$ for an LTL objective $\varphi$ if some general computational strategy for $A$ makes every outcome path in every model of $\mathcal{M}$ satisfy $\varphi$ and has running time bounded by a function in the complexity class $\mathcal{C}$. *Model checking* takes a terminating Turing machine generating $M_k$ from $k$, an LTL formula $\varphi$, a coalition $A$ and a class $\mathcal{C}$, and asks whether $A$ has uniform $\mathcal{C}$-ability for $\varphi$ (Definition 5.1). In the results below the class $\mathcal{C}$ is fixed, and only the generator, the formula and the coalition are input.

**Theorem (Dima and Jamroga).**

1. For every fixed class $\mathcal{C}$ of time bounds that contains the linear bounds $O(n)$, model checking of uniform $\mathcal{C}$-abilities is undecidable, even for singleton coalitions and safety objectives (Theorem 5.2).
2. With $\mathcal{C}$ the polynomial-time bounds, model checking of computational abilities is undecidable even for coalitions of size $2$ and safety objectives, over model templates consisting of a single game (Theorem 5.3).

For a single game, uniform ability and the paper's adaptive ability coincide, so part 2 covers both variants.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Formulas of linear temporal logic](../../../../Logic/temporal-logic/linear-temporal-logic/formula.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

For part 1, the template generated from a deterministic Turing machine consists of the finite prefixes of its unique run from the empty tape, with one agent having a single idle action and accepting configurations labeled; the only strategy, of constant complexity, enforces "always not accepting" exactly when the machine does not halt. For part 2, the proof recalls an earlier undecidability construction for imperfect-information games: from a machine $M$ it builds a three-agent iCGS in which the adversary picks a tape cell, and agents $1$ and $2$ must simulate the evolution of that cell and of the head along the run of $M$; the coalition $\{1, 2\}$ can keep the proposition $\mathit{ok}$ true forever exactly when $M$ never halts, and the paper shows that the winning strategy can be implemented in polynomial time. A good expansion links pages for the undecidability of halting of deterministic Turing machines started on the blank tape and for the Dima–Tiplea encoding of Turing machine runs into three-agent iCGS with imperfect information, from which the proof of Theorem 5.3 starts.

## Sources

- Catalin Dima and Wojciech Jamroga, "Computationally Feasible Strategies", Proceedings of the 22nd International Conference on Autonomous Agents and Multiagent Systems (AAMAS 2023), pp. 784–792, 2023, <https://doi.org/10.65109/xzdv5972>; Definition 2.1 (iCGS) and Definitions 3.1 to 3.11 (model templates, computational strategies, their complexity and uniform ability), Definition 4.3 (adaptive ability), and Definition 5.1 (model checking) with Theorem 5.2 in Section 5.2 and Theorem 5.3 in Section 5.3 of Section 5 ("Model Checking for Computational Strategies") of arXiv:2310.17234v1, read at <https://arxiv.org/abs/2310.17234v1>.
