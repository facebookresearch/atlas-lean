# Ambiguity can strictly benefit the principal, and optimal ambiguous contracts use single-outcome payments

There are principal-agent instances in which the best consistent ambiguous contract gives the principal strictly higher utility than every (unambiguous) contract. The gain from ambiguity can be arbitrarily large: the ratio between the optimal ambiguous and optimal unambiguous principal utilities is unbounded over instances. For every instance there is an optimal consistent ambiguous contract all of whose components are single-outcome payment contracts, each paying a positive amount on exactly one outcome and zero elsewhere; there is a characterization of the ambiguity-proof classes of contracts, for which the principal cannot gain from ambiguity; and if the agent may choose mixed actions, ambiguous contracts give no advantage.

## Proof sketch

Ambiguity allows the principal to deter deviations to action $k$ with one contract and deviations to action $k'$ with another, while the agent's chosen action pays the same under both, relaxing the incentive constraints from a single payment vector to a family. Given an action to implement, replacing each component by contracts that pay only on an outcome maximizing the likelihood ratio against the relevant deviation preserves deterrence and consistency, which yields the single-outcome structure. With mixed actions, the agent's max-min problem becomes a zero-sum game whose minimax value equals what a single contract can enforce, removing the advantage.

## Depends on

- [Ambiguous contract and max-min agent](ambiguous-contract.md)
- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)

## Proof depends on

- [Optimal contracts via one linear program per action](optimal-contract-min-pay-linear-programs.md)
- [Implementable actions are exactly those not replicated more cheaply by a mixture](implementable-action-characterization.md)
- [Von Neumann's minimax theorem](../../noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- P. Dütting, M. Feldman, D. Peretz, L. Samuelson, "Ambiguous Contracts", EC 2023; Econometrica 92(6) (2024), arXiv:2302.07621.
