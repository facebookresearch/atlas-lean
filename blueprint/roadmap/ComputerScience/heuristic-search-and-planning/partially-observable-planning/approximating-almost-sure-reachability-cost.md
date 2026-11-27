# Approximating the optimal cost of almost-sure reachability in POMDPs is undecidable

In a partially observable Markov decision process with integer costs, the least expected total cost of reaching a target almost surely cannot be approximated algorithmically, additively or multiplicatively, for any precision $\epsilon > 0$; already deciding whether this optimal cost is $-\infty$ or $1$ is undecidable.

**Setting (Chatterjee, Chmelík, Gupta and Kanodia).** A POMDP is a tuple $G = (S, A, \delta, Z, \mathcal{O}, \lambda_0)$ with a finite set $S$ of states, a finite set $A$ of actions, a probabilistic transition function $\delta : S \times A \to \mathcal{D}(S)$, a finite set $Z$ of observations, an observation function $\mathcal{O} : S \to Z$ and an initial distribution $\lambda_0$ whose support lies in a single observation class. A *play* is an infinite sequence $s_0 a_0 s_1 a_1 \dots$ with $s_0$ in the support of $\lambda_0$ and $\delta(s_i, a_i)(s_{i+1}) > 0$ for all $i$. A *strategy* maps each finite prefix of a play to a distribution on $A$ and is *observation-based*: two prefixes with the same sequence of observations and actions receive the same distribution. A strategy $\sigma$ and $\lambda_0$ determine a probability measure $\mathbb{P}^\sigma_{\lambda_0}$ on plays with expectation $\mathbb{E}^\sigma_{\lambda_0}$.

The objective has a set $T \subseteq S$ of absorbing target states and a cost function $c : S \times A \to \mathbb{Z}$ with $c(t, a) = 0$ for $t \in T$. The total cost of a play is $\mathrm{Total}(s_0 a_0 s_1 a_1 \dots) = \sum_{i \ge 0} c(s_i, a_i)$. A strategy is *almost-sure winning* if it reaches $T$ with probability $1$; its value is $\mathrm{val}(\sigma) = \mathbb{E}^\sigma_{\lambda_0}[\mathrm{Total}]$, and the *optimal cost* is

$$
\mathrm{optCost} = \inf \{\, \mathrm{val}(\sigma) : \sigma \text{ observation-based and almost-sure winning} \,\}.
$$

For $\epsilon > 0$, the *additive approximation problem* asks to compute an almost-sure winning strategy $\sigma$ with $\mathrm{val}(\sigma) \le \mathrm{optCost} + \epsilon$, and the *multiplicative approximation problem* one with $\mathrm{val}(\sigma) \le \mathrm{optCost} \cdot (1 + \epsilon)$.

**Theorem (Chatterjee, Chmelík, Gupta and Kanodia).** The problem of approximating the optimal cost $\mathrm{optCost}$ in POMDPs with integer costs is undecidable for all $\epsilon > 0$, both for additive and for multiplicative approximation.

The proof shows that, for POMDPs with integer costs (already with a single observation, costs depending only on the state and taking values in $\{-1, 0, 1\}$), no algorithm decides whether $\mathrm{optCost} = -\infty$ or $\mathrm{optCost} = 1$, given that one of the two holds. In contrast, for positive costs $c : S \times A \to \mathbb{N}$ both approximation problems are decidable (Theorem 2 of the copy read).

## Depends on

- [Finite POMDPs](finite-pomdps.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)

## Expansion

The reduction is from the strict emptiness problem for probabilistic finite automata: does some finite word $w$ have acceptance probability greater than $\frac{1}{2}$? A probabilistic automaton is a POMDP with one observation. From an automaton with states $Q$, final states $F$ and initial state $q_0$ one builds a POMDP with states $Q \times \{-1, 1\} \cup \{\mathit{good}, \mathit{bad}, t\}$, initial state $(q_0, 1)$, a single observation, and three new actions. One new action moves $(q, 1)$ to $(q, -1)$, and the letters of the automaton move $(q, -1)$ to $(q', 1)$ with the automaton's probabilities, so each simulated letter costs $1 - 1 = 0$. A second new action leads from $(q, -1)$ to $\mathit{good}$ (cost $-1$) if $q \in F$ and to $\mathit{bad}$ (cost $1$) otherwise, and from either back to the initial state; a third action moves the initial state to the absorbing target $t$, and unavailable actions lead to a losing absorbing state of cost $1$. If some word is accepted with probability greater than $\frac{1}{2}$, repeating it makes each round have negative expected cost, so repeating it many times before stopping drives the expected total cost to $-\infty$ while still reaching $t$ almost surely; otherwise every almost-sure winning strategy has expected cost at least $1$, and the optimal cost is $1$. An approximation algorithm would separate the two cases.

## Sources

- Krishnendu Chatterjee, Martin Chmelík, Raghav Gupta and Ayush Kanodia, "Optimal cost almost-sure reachability in POMDPs", Artificial Intelligence 234, pp. 26–48, 2016, <https://doi.org/10.1016/j.artint.2016.01.007>; conference version "Optimal Cost Almost-Sure Reachability in POMDPs", Proceedings of the AAAI Conference on Artificial Intelligence 29(1), 2015, <https://doi.org/10.1609/aaai.v29i1.9683>. Read in arXiv:1411.3880v1, <https://arxiv.org/abs/1411.3880v1>: Section 2 (POMDPs, observation-based strategies, total-cost objectives, optimal cost and its approximations), Section 3 (the reduction, Lemmas 1–3) and Theorem 1 (main statement), Theorem 2 (positive costs), numbered as in arXiv:1411.3880v1.
