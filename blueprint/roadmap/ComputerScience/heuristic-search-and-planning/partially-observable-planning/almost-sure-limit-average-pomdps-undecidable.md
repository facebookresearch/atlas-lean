# Almost-sure winning for limit-average objectives in POMDPs is undecidable

In partially observable Markov decision processes with rewards in $[0,1]$, deciding whether the controller can make the long-run average reward exceed $1/2$ with probability $1$ is undecidable, already for finite-memory controllers; for the objective "long-run average equal to $1$" it is undecidable for infinite-memory controllers.

**Setting.** A POMDP has a finite set $S$ of states, a finite set $A$ of actions, a probabilistic transition function $\delta : S \times A \to \mathcal{D}(S)$, a finite set of observations with an observation function $\gamma : S \to \mathcal{O}$, and an initial distribution. Strategies are observation-based: the distribution over actions depends only on the sequence of observations and actions so far; a strategy is finite-memory if it can be implemented with a finite set of memory states. For a reward function $r : S \times A \to [0,1]$ and a play $\rho = s_0 a_0 s_1 a_1 \dots$,

$$
\mathrm{LimAvg}(\rho) = \liminf_{n \to \infty} \frac{1}{n} \sum_{i=0}^{n} r(s_i, a_i).
$$

The objectives are $\mathrm{LimAvg}_{=1} = \{\rho : \mathrm{LimAvg}(\rho) = 1\}$ and $\mathrm{LimAvg}_{>1/2} = \{\rho : \mathrm{LimAvg}(\rho) > 1/2\}$; a strategy is *almost-sure winning* if it satisfies the objective with probability $1$.

**Theorem (Chatterjee and Chmelík).**

1. Given a POMDP with rewards, it is undecidable whether there is a finite-memory almost-sure winning strategy for $\mathrm{LimAvg}_{>1/2}$; the same holds for infinite-memory strategies.
2. Given a POMDP with rewards, it is undecidable whether there is an infinite-memory almost-sure winning strategy for $\mathrm{LimAvg}_{=1}$.

In contrast, the existence of a finite-memory almost-sure winning strategy for $\mathrm{LimAvg}_{=1}$ is EXPTIME-complete.

## Depends on

- [Finite POMDPs](finite-pomdps.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)
- [The value-1 problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/value-1-problem-for-probabilistic-automata.md)

## Expansion

Both proofs reduce from problems on probabilistic finite automata (PFA), which are POMDPs with a single observation run for finitely many steps. Part 1 reduces from strict emptiness, whether some word is accepted with probability greater than $1/2$, undecidable by Paz: from a PFA one builds a POMDP with Boolean rewards in which some word is accepted with probability greater than $1/2$ exactly when a finite-memory almost-sure winning strategy for $\mathrm{LimAvg}_{>1/2}$ exists. Part 2 reduces from the value-1 problem, whether words are accepted with probability arbitrarily close to $1$, undecidable by Gimbert and Oualhadj: the POMDP adds a state $\mathit{good}$ with reward $1$ and a state $\mathit{bad}$ with reward $0$, entered from final and non-final states respectively by a new action that later returns to the initial state, all in one observation.

## Sources

- Krishnendu Chatterjee and Martin Chmelík, "POMDPs under Probabilistic Semantics", Artificial Intelligence 221, pp. 46–72, 2015, <https://doi.org/10.1016/j.artint.2014.12.009>; the definitions of Section 2, Theorem 3 of Section 3 (EXPTIME-completeness for finite-memory strategies and $\mathrm{LimAvg}_{=1}$), Theorem 4 of Section 4 (finite-memory strategies with quantitative constraint) and Theorem 5 of Section 5 (infinite-memory strategies with qualitative constraint), of arXiv:1308.4846v1 (the copy read), <https://arxiv.org/abs/1308.4846v1>.
