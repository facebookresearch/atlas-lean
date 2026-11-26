# Linear contracts approximate the optimal contract within the number of actions, tightly

In every principal-agent instance with $n$ actions, the best linear contract yields principal utility at least $\frac{1}{n} \max_i (R_i - c_i)$, i.e. at least a $1/n$ fraction of the optimal welfare, and in particular of the optimal contract's utility. Conversely, for every $n$ and $\varepsilon > 0$ there are instances with $n$ actions in which the optimal contract's principal utility exceeds $(n - \varepsilon)$ times that of the best linear contract.

## Proof sketch

Consider the actions on the upper envelope ordered by critical values $\alpha_1 < \dots < \alpha_K$. The welfare $R_i - c_i$ of the welfare-maximizing action telescopes into a sum of increments, each charged to the principal's utility $(1 - \alpha_k) R_{i_k}$ at some critical value; there are at most $n$ terms, giving the factor $n$. The lower-bound instance uses actions with geometrically increasing rewards and costs tuned so that all actions sit on the envelope with equal principal utility under linear contracts, while a non-linear contract paying only on a distinguishing outcome extracts nearly all welfare.

## Depends on

- [Linear contract and its critical values](linear-contract-critical-values.md)
- [Optimal contracts via one linear program per action](optimal-contract-min-pay-linear-programs.md)

## Proof depends on

- [Monotonicity of best responses along linear contracts](linear-contract-best-response-monotonicity.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
