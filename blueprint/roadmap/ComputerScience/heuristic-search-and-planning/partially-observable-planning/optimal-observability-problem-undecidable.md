# The optimal observability problem for POMDPs is undecidable

Given a Markov decision process, a budget of observations and a reward threshold, it is undecidable whether some observation function with at most that many observations turns it into a partially observable process whose minimal expected reward stays within the threshold. Restricted to positional strategies the problem becomes decidable.

**Setting (Konsta, Lluch Lafuente and Matheja).** A *Markov decision process* $M = (S, I, G, \mathit{Act}, P, \mathit{rew})$ has finite sets of states $S$, uniformly distributed initial states $I \subseteq S$, goal states $G \subseteq S$ and actions $\mathit{Act}$, a transition probability function $P : S \times \mathit{Act} \to \mathrm{Dist}(S)$ and a reward function $\mathit{rew} : S \to \mathbb{R}_{\ge 0}$ on states. A *strategy* maps nonempty finite state sequences to distributions over actions. The expected reward of a strategy sums, over the paths from an initial state to their first goal state, the path probability times the accumulated reward, divided by $|I|$, and is infinite if the goal is not reached with probability one. Equipping $M$ with an observation function $\mathit{obs} : S \to O \cup \{o_G\}$, with a reserved observation $o_G \notin O$ such that $\mathit{obs}(s) = o_G$ if and only if $s \in G$, yields a POMDP $M[\mathit{obs}]$ whose strategies must be observation-based: they choose the same action distribution on histories with the same observation sequence. $\mathrm{MinExpRew}(M[\mathit{obs}])$ is the infimum of the expected reward over these strategies. The *optimal observability problem* (OOP) asks, given $M$, a budget $B \in \mathbb{N}_{\ge 1}$ and a threshold $\tau \in \mathbb{Q}_{\ge 0}$, whether there is an observation function with $|O| \le B$ such that $\mathrm{MinExpRew}(M[\mathit{obs}]) \le \tau$. As an input to an algorithm, the transition probabilities and rewards of $M$ are rational numbers.

**Theorem (Konsta, Lluch Lafuente and Matheja).** The optimal observability problem is undecidable.

The same paper shows that the problem is NP-complete when strategies are restricted to positional deterministic ones, and decidable in PSPACE for positional randomized strategies.

## Depends on

- [Finite POMDPs](finite-pomdps.md)
- [Markov decision processes and adversaries](../../../Logic/temporal-logic/probabilistic-model-checking/markov-decision-processes-and-adversaries.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from the policy-existence problem for POMDPs: given a POMDP and a rational threshold, is the minimal expected reward over observation-based strategies at most the threshold? Madani, Hanks and Condon proved it undecidable. From a POMDP $(M, O, \mathit{obs})$ and a threshold $\tau$, it builds in polynomial time an MDP $M'$ and takes the budget $B = |O|$ and the same threshold. $M'$ adds a sink state whose positive-probability reachability makes the expected reward infinite; tags every action with an observation, so that in a non-goal state only actions tagged with that state's original observation behave as in $M$ and all others lead to the sink; and adds a new initial state for each observation, which leads to the sink unless an action with its own tag is taken and moves with positive probability to the other new initial states. These gadgets force every admissible observation function to coincide with the original one up to renaming, so the OOP instance is positive exactly when the POMDP's minimal expected reward is at most $\tau$.

## Sources

- Alyzia-Maria Konsta, Alberto Lluch Lafuente and Christoph Matheja, "What Should Be Observed for Optimal Reward in POMDPs?", Computer Aided Verification (CAV 2024), Lecture Notes in Computer Science, pp. 373–394, 2024, <https://doi.org/10.1007/978-3-031-65633-0_17>; Section 2 (Definitions 1 to 5: MDPs, strategies, expected rewards, POMDPs and observation-based strategies), Definition 6 (the optimal observability problem), Theorem 1 and Proposition 1 (policy existence, after Madani et al.) of Section 3, and Theorem 2 (NP-completeness) and Theorem 4 (positional randomized strategies, decidable in ETR and hence in PSPACE) of Section 4, of arXiv:2405.10768v2, read at <https://arxiv.org/abs/2405.10768v2>.
