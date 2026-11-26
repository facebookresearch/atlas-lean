# Constant-factor approximation of multi-agent contracts for submodular and XOS rewards

For multi-agent contract instances with a submodular reward function given by a value oracle, there is a polynomial-time algorithm computing linear contracts whose principal utility is at least a constant fraction of the optimum. The same holds for XOS reward functions (pointwise maxima of additive functions) given value and demand oracles. Constant approximation is best possible for submodular rewards even with value and demand oracles: there is a constant $c > 1$ such that no algorithm using polynomially many such queries achieves a $c$-approximation.

## Proof sketch

Interpret $\sqrt{c_i}$-scaled quantities as prices and use (approximate) demand queries to select a candidate set $S$ in which each agent's marginal contribution is large compared with the square root of its cost times $f(S)$; this keeps $\sum_i c_i / f(i \mid S - i)$ bounded away from $1$. A scaling property of XOS functions and their marginals allows extracting a subset whose value is a constant fraction of the optimum while maintaining this condition. The lower bound uses a family of submodular functions indistinguishable by polynomially many queries.

## Depends on

- [Multi-agent binary-action contract with a team reward function](multi-agent-binary-action-contract.md)
- [Submodular set function](../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Proof depends on

- [The multi-agent contract problem reduces to maximizing a set function](multi-agent-contract-set-function-reduction.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Contracts", STOC 2023, arXiv:2211.05434.
