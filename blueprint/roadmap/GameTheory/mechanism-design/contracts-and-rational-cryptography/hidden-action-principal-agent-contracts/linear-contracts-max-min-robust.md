# Linear contracts are max-min optimal under expected-reward uncertainty

Suppose there are $m \ge 3$ outcomes with rewards $0 = r_1 < \dots < r_m$ (the lowest reward is normalized to $0$), and the principal knows the action costs $c_i$, the rewards $r_j$ and only the expected rewards $R_i$ of the actions, but not the distributions $F_i$ (some distributions with these means exist). Over all limited-liability contracts $t$, the worst-case principal utility (infimum over all distributions with the known means) is maximized by a linear contract. Equivalently, linear contracts are max-min optimal when the principal's knowledge is restricted to first moments of the outcome distributions.

## Proof sketch

For every limited-liability contract $t$ there are distributions with the known means, supported on two outcomes each, under which some affine contract $\alpha_0 + \alpha_1 r$ with $\alpha_0, \alpha_1 \ge 0$ gives the principal at least as much as $t$; since an affine contract's payoff depends only on the means, its worst case is that value. Dropping the constant part $\alpha_0$ does not change the agent's incentives, so the linear contract with parameter $\alpha_1$ does at least as well, and a linear contract's payoff is the same under all distributions with the given means.

## Depends on

- [Linear contract and its critical values](linear-contract-critical-values.md)
- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)

## Proof depends on

- [Monotonicity of best responses along linear contracts](linear-contract-best-response-monotonicity.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713, Theorem 1 (with Assumption A4, $r_1 = 0$).
- G. Carroll, "Robustness and Linear Contracts", American Economic Review 105(2) (2015).
