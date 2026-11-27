# Subadditive multi-agent contracts admit no better than Omega(sqrt(n)) approximation

For multi-agent contract instances with $n$ agents and subadditive reward functions accessible through value and demand oracles, for every randomized algorithm making only polynomially many value and demand queries there is an instance (a subadditive reward function) on which, with high probability, the contract it computes has approximation ratio $\Omega(\sqrt n)$ to the optimal contract. The hard instances can be chosen with reward functions that are within a constant factor of submodular functions.

## Proof sketch

Give all agents the same cost and start from a symmetric subadditive reward function under which every set of fewer than $\sqrt n$ agents gives the principal $O(1)$ and every larger set gives at most $0$, because the required shares $c_i / f(i \mid S \setminus \{i\})$ exhaust the reward. Raise the value of one hidden random set $T$ of $n/2 + 1$ agents, keeping the function monotone and subadditive (and within a constant factor of submodular), so that $T$ gives the principal $\Omega(\sqrt n)$ while every other set still gives $O(1)$. Each value or demand query reveals information about only polynomially many candidate sets, so polynomially many queries find $T$ only with negligible probability. By Yao's principle it suffices to analyse an arbitrary deterministic algorithm on this random instance.

## Depends on

- [Multi-agent binary-action contract with a team reward function](multi-agent-binary-action-contract.md)
- [XOS set functions, demand queries and value queries](xos-functions-demand-and-value-queries.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Proof depends on

- [The multi-agent contract problem reduces to maximizing a set function](multi-agent-contract-set-function-reduction.md)
- [Yao's minimax principle](../../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Contracts", STOC 2023, arXiv:2211.05434, Theorem 4.4.
