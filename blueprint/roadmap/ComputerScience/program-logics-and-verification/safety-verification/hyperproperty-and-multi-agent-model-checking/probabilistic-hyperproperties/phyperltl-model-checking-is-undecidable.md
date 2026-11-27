# Model checking PHyperLTL is undecidable

PHyperLTL asserts the existence of policies for several agents that run in independent copies of one Markov decision process, and constrains probabilities of LTL properties of the joint behavior. Its model checking problem is undecidable, already with a single probability constraint.

**Setting (Pontiggia, Macák, Andriushchenko, Chiari and Češka).** A policy of an MDP $M$ is a deterministic function from finite paths to actions. The $m$-self-composition $M^m$ runs $m$ independent copies of $M$ simultaneously. PHyperLTL formulas have the form

$$
\exists (\pi_1 \dots \pi_n).\ Q_1 s_1 \in I_1(\pi_{j_1}) \dots Q_m s_m \in I_m(\pi_{j_m}).\ \phi, \qquad \phi ::= \phi \wedge \phi \mid \neg \phi \mid \mathbb{P}(\varphi) \bowtie c,
$$

with policy variables $\pi_i$, state variables $s_i$, $n \le m$, quantifiers $Q_i \in \{\exists, \forall\}$, sets $I_i$ of states, $c \in [0, 1]$, and LTL formulas $\varphi$ over atoms $a_{s_i}$ (proposition $a$ evaluated in copy $i$). The formula holds in $M$ if there are policies for $\pi_1, \dots, \pi_n$ such that, choosing initial states $s_i \in I_i$ existentially or universally as prescribed, with copy $i$ controlled by the policy of $\pi_{j_i}$, the Boolean combination of constraints $\Pr(\varphi) \bowtie c$, evaluated in the Markov chain induced on $M^m$, is true. Model checking asks whether a given finite MDP satisfies a given well-formed formula.

**Theorem (Pontiggia, Macák, Andriushchenko, Chiari and Češka).** PHyperLTL model checking is undecidable.

The proof uses a formula with a single probability constraint; the authors note that the earlier undecidability proofs for the logics PHL and HyperPCTL need two constraints or nested probability operators, which PHyperLTL lacks. As a corollary, planning for factored, observation-independent, locally fully observable decentralized MDPs under the infinite-horizon total reward criterion is undecidable.

## Depends on

- [Markov decision processes and adversaries](../../../../../Logic/temporal-logic/probabilistic-model-checking/markov-decision-processes-and-adversaries.md)
- [Discrete-time Markov chains](../../../../../Logic/temporal-logic/probabilistic-model-checking/discrete-time-markov-chains.md)
- [Formulas of linear temporal logic](../../../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)

## Expansion

The reduction is from emptiness of probabilistic finite automata: given an automaton with an absorbing accepting state and a threshold $\lambda \in (0, 1)$, whether some word is accepted with probability greater than $\lambda$. The constructed MDP is the disjoint union of a part that mimics runs of the automaton, with its input letters as actions and states recording the last letter read, and a deterministic part that only records the letters chosen; a formula with a single probability constraint, over agents started in the two parts, holds exactly when some word is accepted with probability greater than $\lambda$.

## Sources

- Francesco Pontiggia, Filip Macák, Roman Andriushchenko, Michele Chiari and Milan Češka, "Decentralized Planning Using Probabilistic Hyperproperties", Proceedings of the 24th International Conference on Autonomous Agents and Multiagent Systems (AAMAS 2025), pp. 1688–1697, IFAAMAS, 2025, <https://doi.org/10.65109/vnon1089>; Theorem 3.1 with the proof in the appendix "Undecidability of PHyperLTL", the syntax and semantics of Section 3 (Sections 3.1 and 3.2), Definition 2.3 (factored, observation-independent, locally fully observable Dec-MDPs), and Corollary 5.1 of Section 5 of arXiv:2502.13621v1 (the copy read), <https://arxiv.org/abs/2502.13621v1>.
