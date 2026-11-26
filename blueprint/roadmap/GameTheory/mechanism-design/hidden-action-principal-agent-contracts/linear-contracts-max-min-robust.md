# Linear contracts are max-min optimal under expected-reward uncertainty

Suppose the principal knows the action costs $c_i$, the rewards $r_j$ and only the expected rewards $R_i$ of the actions, but not the distributions $F_i$. Over all contracts $t$, the worst-case principal utility (infimum over all instances consistent with the known data) is maximized by a linear contract. Equivalently, linear contracts are max-min optimal when the principal's knowledge is restricted to first moments of the outcome distributions.

## Proof sketch

Given any contract $t$, an adversary can choose distributions consistent with the known means that concentrate on outcomes where $t$ pays the most relative to reward; the agent's induced payment then behaves as if the contract were the lower concave envelope of $t$ viewed as a function of reward. A linear function dominates such envelopes in the worst case, and one checks via a minimax argument over the adversary's choices that the best linear contract matches the best worst-case value.

## Depends on

- [Linear contract and its critical values](linear-contract-critical-values.md)

## Proof depends on

- [Monotonicity of best responses along linear contracts](linear-contract-best-response-monotonicity.md)
- [Von Neumann's minimax theorem](../../noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
- G. Carroll, "Robustness and Linear Contracts", American Economic Review 105(2) (2015).
