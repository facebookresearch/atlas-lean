# Linear contracts approximate the optimal contract within the number of actions, tightly

In every principal-agent instance with $n$ actions, one of which has cost $0$, the best linear contract yields principal utility at least $\frac{1}{N} \max_i (R_i - c_i) \ge \frac1n \max_i (R_i - c_i)$, where $N \le n$ is the number of actions implementable by some linear contract; that is, at least a $1/n$ fraction of the optimal welfare, and in particular of the optimal contract's utility. Conversely, for every $n$ and $\varepsilon > 0$ there are instances with $n$ actions and $n$ outcomes satisfying the monotone likelihood ratio property in which the optimal contract's principal utility is at least $(n - \varepsilon)$ times that of the best linear contract.

## Proof sketch

Consider the actions on the upper envelope ordered by critical values $\alpha_1 < \dots < \alpha_K$. The welfare-maximizing action is the last linearly implementable action $a_N$, and $R_N - c_N \le \sum_{k=1}^N (1 - \alpha_k) R_k$, where $(1 - \alpha_k) R_k$ is the principal's utility from the linear contract at the critical value $\alpha_k$ implementing $a_k$; there are $N \le n$ terms, giving the factor $N$. The lower-bound instance has full information: action $i$ leads deterministically to its own outcome, with rewards growing geometrically ($R_{i+1} = R_i / \varepsilon$) and costs defined recursively, so that every linear contract gives the principal at most about $1$, while the contract paying $c_i$ on outcome $i$ extracts welfare about $n$.

## Depends on

- [Linear contract and its critical values](linear-contract-critical-values.md)
- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)

## Proof depends on

- [Monotonicity of best responses along linear contracts](linear-contract-best-response-monotonicity.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713, Theorems 2 and 3.
