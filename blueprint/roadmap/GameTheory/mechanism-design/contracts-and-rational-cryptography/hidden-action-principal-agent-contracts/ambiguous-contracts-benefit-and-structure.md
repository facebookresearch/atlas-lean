# Ambiguity can strictly benefit the principal, and optimal ambiguous contracts use single-outcome payments

There are principal-agent instances in which the best consistent incentive-compatible ambiguous contract gives the principal strictly higher utility than every (unambiguous) contract. When rewards may be negative the gain is unbounded: in some instances the best classic contract gives the principal $0$ while an ambiguous contract gives her a positive utility. For instances with $n \ge 2$ actions and nonnegative rewards, the ratio between the optimal ambiguous and the optimal classic principal utilities is at most $n - 1$, and this is tight.

Structure: if $n \ge 2$, every incentive-compatible ambiguous contract $\langle \tau, i \rangle$ with $T_i(\tau) > 0$ can be replaced by an incentive-compatible ambiguous contract implementing $i$ at the same expected payment $T_i(\tau)$ with at most $\min\{m, n - 1\}$ components, all of which are single-outcome payment contracts, each paying a positive amount on exactly one outcome and zero elsewhere. If $T_i(\tau) = 0$, the zero-cost action forces $c_i = 0$, and the zero contract alone implements $i$. Since an optimal contract may have expected payment $0$ (for instance when $n = 1$, or when implementing a zero-cost action is best for the principal), where single-outcome payment contracts, which pay a positive amount, do not apply, every instance has an optimal consistent ambiguous contract that is either the zero contract alone or a set of at most $\min\{m, n - 1\}$ single-outcome payment contracts. A class of payment functions, viewed as maps from rewards to nonnegative payments, is ambiguity-proof, meaning that for no instance and action can the principal gain by implementing that action with an ambiguous contract from the class instead of a classic one, if and only if it is ordered: any two of its payment functions $t, t'$ satisfy $t \ge t'$ pointwise or $t \le t'$ pointwise. Finally, if the agent may choose mixed actions, every incentive-compatible ambiguous contract can be replaced by a classic one with the same agent and principal payoffs, so ambiguity gives no advantage.

## Proof sketch

Ambiguity allows the principal to deter deviations to action $k$ with one contract and deviations to action $k'$ with another, while the agent's chosen action pays the same under both, relaxing the incentive constraints from a single payment vector to a family. Given an ambiguous contract implementing action $i$ with expected payment $T_i > 0$, replace it by the single-outcome payment contracts that pay $T_i / F_{i,j}$ on each outcome $j$ with $F_{i,j} > 0$; a deviation to $k$ is then evaluated at the outcome minimizing the likelihood ratio $F_{k,j}/F_{i,j}$, which deters it at least as well, and keeping one component per deviation leaves at most $n - 1$ components. For an ordered class, the pointwise smallest payment function of an ambiguous contract gives every action its worst-case utility, so on its own it implements the same action at the same payment; for an unordered pair a three-action, two-outcome instance makes the third action implementable by the ambiguous contract $\{t, t'\}$ but by no classic contract from the class. With mixed actions, the agent's max-min problem becomes a zero-sum game whose minimax value equals what a single contract can enforce, removing the advantage.

## Depends on

- [Ambiguous contract and max-min agent](ambiguous-contract.md)
- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)

## Proof depends on

- [Optimal contracts via one linear program per action](optimal-contract-min-pay-linear-programs.md)
- [Implementable actions are exactly those not replicated more cheaply by a mixture](implementable-action-characterization.md)
- [Von Neumann's minimax theorem](../../../noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- P. Dütting, M. Feldman, D. Peretz, L. Samuelson, "Ambiguous Contracts", EC 2023; Econometrica 92(6) (2024), arXiv:2302.07621.
