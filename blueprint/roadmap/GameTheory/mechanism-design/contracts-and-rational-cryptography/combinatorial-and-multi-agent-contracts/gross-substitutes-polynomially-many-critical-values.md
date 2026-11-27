# Gross-substitutes success functions have polynomially many critical values

In a combinatorial contract instance whose success function $f$ is gross substitutes, the number of critical values of $\alpha \in [0, 1]$ is at most $\binom{n + 1}{2} = n(n+1)/2$, and they can be enumerated using polynomially many value queries to $f$.

## Proof sketch

The agent's demand at $\alpha$ maximizes $\alpha f(S) - c(S)$, equivalently $f(S) - c(S)/\alpha$, a demand query at prices $c/\alpha$, which for gross-substitutes $f$ is answered by a greedy algorithm with a suitable tie-breaking rule; the next critical value after a given $\alpha$ can be computed from the greedy run in polynomial time. For a generic cost function, for which the greedy run at any $\alpha$ meets at most one tie, rank the actions by cost ($1$ for the cheapest, $n$ for the most expensive) and let $\Phi(S)$ be the sum of the ranks in $S$. The demanded set at each critical value has $\Phi$ at least one larger than at the previous one, and $\Phi \le 1 + 2 + \dots + n = n(n+1)/2$, which bounds the number of critical values. A perturbation argument shows that making $c$ generic can only increase the number of critical values.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Gross-substitutes success-probability function](gross-substitutes-success-probability.md)

## Proof depends on

- [Monotonicity of best responses along linear contracts](../hidden-action-principal-agent-contracts/linear-contract-best-response-monotonicity.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021; SIAM Journal on Computing 54(6) (2025), arXiv:2109.14260.
