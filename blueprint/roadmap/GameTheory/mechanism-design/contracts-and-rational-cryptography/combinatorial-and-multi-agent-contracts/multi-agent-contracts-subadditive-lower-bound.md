# Subadditive multi-agent contracts admit no better than Omega(sqrt(n)) approximation

For multi-agent contract instances with $n$ agents and subadditive reward functions accessible through value and demand oracles, every algorithm making polynomially many queries has approximation ratio $\Omega(\sqrt n)$ on some instance. The hard instances can be chosen with reward functions that are within a constant factor of submodular functions.

## Proof sketch

Hide a special set of about $\sqrt n$ agents whose joint reward is high, while every other set of comparable size has reward close to that of a symmetric submodular function. Queries reveal information about the special set only with negligible probability, so the algorithm must essentially choose a set without knowing it; the principal's utility from any set not aligned with the special set is smaller by a factor $\Omega(\sqrt n)$ because the required shares $c_i / f(i \mid S - i)$ exhaust the reward.

## Depends on

- [Multi-agent binary-action contract with a team reward function](multi-agent-binary-action-contract.md)
- [XOS set functions, demand queries and value queries](xos-functions-demand-and-value-queries.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Proof depends on

- [The multi-agent contract problem reduces to maximizing a set function](multi-agent-contract-set-function-reduction.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Contracts", STOC 2023, arXiv:2211.05434.
