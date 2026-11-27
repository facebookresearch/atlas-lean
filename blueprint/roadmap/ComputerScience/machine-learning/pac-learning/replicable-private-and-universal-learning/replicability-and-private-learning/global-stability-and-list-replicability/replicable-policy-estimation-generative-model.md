# Replicable policy estimation in discounted tabular MDPs with a generative model

Consider a discounted Markov decision process with $N$ state-action pairs and discount $\gamma$, accessed through a generative model. Call an algorithm $\rho$-replicable if two executions on independent samples with the same internal randomness output the same policy with probability at least $1 - \rho$. There is an efficient $\rho$-replicable algorithm that outputs an $\varepsilon$-optimal policy with probability $1-\delta$ using

$$
\tilde O\!\left(\frac{N^3 \log(1/\delta)}{(1-\gamma)^5 \varepsilon^2 \rho^2}\right)
$$

samples, and every deterministic $\rho$-replicable algorithm needs $\Omega\big(N^3 / ((1-\gamma)^3 \varepsilon^2 \rho^2)\big)$ samples. Relaxing replicability to TV indistinguishability improves the sample complexity to $\tilde O\big(N^2 \log(1/\delta)/((1-\gamma)^5 \varepsilon^2 \rho^2)\big)$. Replicable variants of parallel value iteration and of R-max in the episodic setting also exist.

## Proof sketch

Estimate each transition and reward to accuracy $\varepsilon(1-\gamma)^2$ with replicable rounding at level $\rho/N$, so that all $N$ rounded estimates coincide across runs; planning in the rounded model is deterministic, so the output policy coincides. The union bound over $N$ coordinates costs the extra factor $N^2$ in samples per coordinate. The lower bound reduces from $N$ independent replicable coin problems, each requiring $\Omega(1/(\tau^2\rho_i^2))$ samples with $\sum_i \rho_i \le \rho$.

## Depends on

- [Markov decision process](../../../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Optimal value of a discounted Markov decision process](../../../../../heuristic-search-and-planning/value-iteration/optimal-value.md)
- [Total-variation indistinguishable learning rules](tv-indistinguishable-learning-rule.md)

## Proof depends on

- [Replicability costs a quadratic factor in the replicability parameter](replicable-coin-problem-lower-bound.md)
- [Generative-model sample bound (restricted, non-minimax)](../../../../reinforcement-learning/generative-model-sample-bound.md)
- [TV indistinguishability, replicability and approximate privacy are equivalent for PAC learning](tv-indistinguishability-replicability-privacy-equivalence.md)

## Sources

- A. Karbasi, G. Velegkas, L. F. Yang, F. Zhou, "Replicability in Reinforcement Learning", NeurIPS (2023), arXiv:2305.19562.
- E. Eaton, M. Hussing, M. Kearns, J. Sorrell, "Replicable Reinforcement Learning", NeurIPS (2023), arXiv:2305.15284.
