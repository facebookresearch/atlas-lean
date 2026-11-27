# Optimal combinatorial contracts: polynomial for gross substitutes, NP-hard for submodular

For combinatorial contract instances with binary outcome and additive costs: if the success function $f$ is gross substitutes, an optimal contract can be computed with polynomially many value queries and polynomial running time; if $f$ is submodular, computing an optimal contract is NP-hard, already for budget-additive $f(S) = \min\{B, \sum_{i \in S} f(\{i\})\}$ given explicitly by integer values $f(\{1\}), \dots, f(\{n\})$ and $B$ (after scaling into $[0, 1]$). The positive result extends to linear contracts for higher-dimensional outcome spaces, which are robustly optimal given first-moment constraints.

## Proof sketch

For gross substitutes, the optimal contract is one of the critical values; enumerate them one after another (each next critical value is computable from a greedy demand computation), evaluate the principal's utility at each, and take the best; there are polynomially many. For submodular $f$, reduce from Subset Sum with numbers $x_1, \dots, x_n < Z$: set $f(S) = \min\{Z, \sum_{i \in S} x_i\}$ and $c(i) = x_i / Z^2$. If some subset sums to exactly $Z$, the contract $\alpha = 1/Z^2$ induces it and gives the principal $(1 - 1/Z^2) Z$; otherwise there are exactly two critical values, and both give the principal strictly less, so the optimal principal utility decides the Subset Sum instance.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Gross-substitutes success-probability function](gross-substitutes-success-probability.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [Linear contract and its critical values](../hidden-action-principal-agent-contracts/linear-contract-critical-values.md)

## Proof depends on

- [Gross-substitutes success functions have polynomially many critical values](gross-substitutes-polynomially-many-critical-values.md)
- [With a binary outcome, contracts paying only on success are without loss](binary-outcome-pay-on-success.md)
- [SUBSET-SUM is NP-complete](../../../../TheoryOfComputation/np-completeness/number-and-packing-problems/subset-sum/part-06/subset-sum-dec-np-complete.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021; SIAM Journal on Computing 54(6) (2025), arXiv:2109.14260.
- T. Ezra, M. Feldman, M. Schlesinger, "On the (In)approximability of Combinatorial Contracts", ITCS 2024.
