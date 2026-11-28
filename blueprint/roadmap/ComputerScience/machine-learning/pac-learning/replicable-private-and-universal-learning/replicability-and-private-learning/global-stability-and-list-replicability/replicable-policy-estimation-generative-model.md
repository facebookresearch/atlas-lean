# Replicable policy estimation in discounted tabular MDPs with a generative model

Consider a discounted Markov decision process with finitely many states, $N$ state-action pairs, rewards $r(s,a) \in [0,1]$ and discount $\gamma \in (0,1)$ (Karbasi et al., Definition 2.1), so that values lie in $[0, 1/(1-\gamma)]$, accessed through a generative model. The reward scale matters: multiplying all rewards by $R$ multiplies every value and every additive value error by $R$, so the bounds below are for this normalization. Call an algorithm $\rho$-replicable if two executions on independent samples with the same internal randomness output the same policy with probability at least $1 - \rho$. For $\varepsilon, \rho \in (0,1)$ and $\delta \in (0, \rho/3)$ there is an efficient locally random $\rho$-replicable algorithm (each output coordinate uses only its own independent random string) that outputs an $\varepsilon$-optimal policy with probability $1-\delta$ using

$$
\tilde O\!\left(\frac{N^3 \log(1/\delta)}{(1-\gamma)^5 \varepsilon^2 \rho^2}\right)
$$

samples. Conversely (Theorem D.11), with $\delta = 1/4$, every deterministic $\rho$-replicable algorithm that outputs a randomized policy $\pi$ such that for each state $s$ separately $\Pr\big[|V^\pi(s) - V^\star(s)| \le \varepsilon\big] \ge 1 - \delta/12$ needs $\Omega\big(N^3 / ((1-\gamma)^3 \varepsilon^2 \rho^2)\big)$ samples on some MDP with rewards in $[0,1]$; the premise is a per-state guarantee, weaker than accuracy at all states simultaneously with that probability, so the lower bound applies in particular to algorithms with the simultaneous guarantee. The accuracy requirement is essential, since a fixed constant policy is replicable with zero samples. Relaxing replicability to TV indistinguishability improves the sample complexity to $\tilde O\big(N^2 \log(1/\delta)/((1-\gamma)^5 \varepsilon^2 \rho^2)\big)$ for $\delta \in (0, \rho/5)$, and coupling the outputs of that algorithm through shared randomness gives a $\rho$-replicable algorithm, no longer locally random, with the same $\tilde O(N^2)$ dependence for $\delta \in (0, \rho/4)$. Replicable variants of parallel value iteration and of R-max in the episodic setting also exist.

## Proof sketch

Estimate each transition and reward to accuracy $\varepsilon(1-\gamma)^2$ with replicable rounding at level $\rho/N$, so that all $N$ rounded estimates coincide across runs; planning in the rounded model is deterministic, so the output policy coincides. The union bound over $N$ coordinates costs the extra factor $N^2$ in samples per coordinate. The lower bound reduces from $N$ independent replicable coin problems, each requiring $\Omega(1/(\tau^2\rho_i^2))$ samples with $\sum_i \rho_i \le \rho$.

## Depends on

- [Markov decision process](../../../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Optimal value of a discounted Markov decision process](../../../../../heuristic-search-and-planning/value-iteration/optimal-value.md)
- [Total-variation indistinguishable learning rules](tv-indistinguishable-learning-rule.md)
- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)

## Proof depends on

- [Replicability costs a quadratic factor in the replicability parameter](replicable-coin-problem-lower-bound.md)
- [Generative-model sample bound (restricted, non-minimax)](../../../../reinforcement-learning/generative-model-sample-bound.md)
- [TV indistinguishability, replicability and approximate privacy are equivalent for PAC learning](tv-indistinguishability-replicability-privacy-equivalence.md)

## Sources

- A. Karbasi, G. Velegkas, L. F. Yang, F. Zhou, "Replicability in Reinforcement Learning", NeurIPS (2023), arXiv:2305.19562, Definitions 2.1, 2.8, 2.10 and B.4, Theorem 3.1, Corollary 3.2, Corollaries 4.4 and 4.10 and Theorem D.11.
- E. Eaton, M. Hussing, M. Kearns, J. Sorrell, "Replicable Reinforcement Learning", NeurIPS (2023), arXiv:2305.15284.
