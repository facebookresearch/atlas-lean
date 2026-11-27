# Constant-factor approximation of multi-agent contracts for submodular and XOS rewards

For multi-agent contract instances with a submodular reward function given by a value oracle, there is a polynomial-time algorithm computing linear contracts whose principal utility is at least a constant fraction of the optimum. The same holds for XOS reward functions (pointwise maxima of additive functions) given value and demand oracles. Constant approximation is best possible for submodular rewards even with value and demand oracles: there is a constant $\eta > 1$ such that every (possibly randomized) algorithm making subexponentially many value and demand queries returns an $\eta$-approximately optimal contract only with probability exponentially small in $n$.

## Proof sketch

For an optimal set $S^\star$ and every $S \subseteq S^\star$, $\sum_{i \in S} \sqrt{c_i} \le \sqrt{f(S)}$, and any set $S$ with $f(i \mid S \setminus \{i\}) \ge \sqrt{2 c_i f(S)}$ for all $i \in S$ gives the principal at least $f(S)/2$. With prices $p_i = \tfrac12 \sqrt{c_i f(S^\star)}$ (using a guess of $f(S^\star)$), a demand set $T$ has $f(T) \ge \tfrac12 f(S^\star)$ and marginals at least $p_i$. A scaling property of XOS functions and their marginals then extracts $U \subseteq T$ with $f(U)$ a constant fraction of $f(S^\star)$ and marginals at least half those in $T$, so $U$ meets the condition and yields a constant fraction of the optimum; for submodular $f$, approximate demand sets computed from value queries suffice. The lower bound uses a family of submodular functions indistinguishable by polynomially many queries.

## Depends on

- [Multi-agent binary-action contract with a team reward function](multi-agent-binary-action-contract.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [XOS set functions, demand queries and value queries](xos-functions-demand-and-value-queries.md)

## Proof depends on

- [The multi-agent contract problem reduces to maximizing a set function](multi-agent-contract-set-function-reduction.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Contracts", STOC 2023, arXiv:2211.05434, Theorems 3.1 and 4.1.
- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Combinatorial Contracts", SODA 2025 (where the submodular lower bound first appeared).
