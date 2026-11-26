# Optimal combinatorial contracts need exponentially many demand queries for submodular rewards

In combinatorial contract instances with binary outcome, additive costs $c$ and a submodular success function $f$, no algorithm using polynomially many value queries achieves a constant-factor approximation of the optimal principal utility, and finding an optimal contract requires exponentially many demand queries to $f$ (queries returning $\arg\max_S \alpha f(S) - c(S)$ for chosen $\alpha$ and prices). The same exponential lower bound holds for other combinations of submodular or supermodular $f$ and $c$, and extends to arbitrary communication protocols between the principal and oracles for $f$ and $c$; in contrast, for gross-substitutes $f$ and additive $c$ an optimal contract is computable with polynomially many value queries.

## Proof sketch

Build equal-revenue instances: families of success functions for which the principal's utility $(1 - \alpha) f(S_\alpha)$ is nearly constant across all critical values, except at one hidden critical value where it is larger. With $f$ submodular and $c$ additive, such functions can have exponentially many critical values, and a sparse-demand property ensures that each demand query reveals information about only a few critical values, so exponentially many queries are needed to find the hidden one; a communication-complexity reduction from set disjointness extends the bound to general protocols.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Submodular set function](../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [Gross-substitutes success-probability function](gross-substitutes-success-probability.md)
- [XOS set functions, demand queries and value queries](xos-functions-demand-and-value-queries.md)

## Proof depends on

- [Optimal combinatorial contracts: polynomial for gross substitutes, NP-hard for submodular](combinatorial-contracts-gross-substitutes-vs-submodular.md)

## Sources

- P. Dütting, M. Feldman, Y. Gal-Tzur, A. Rubinstein, "When Contracts Get Complex: Information-Theoretic Barriers", SODA 2026, arXiv:2403.09794.
- T. Ezra, M. Feldman, M. Schlesinger, "On the (In)approximability of Combinatorial Contracts", ITCS 2024.
- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021, arXiv:2109.14260.
