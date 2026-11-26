# Optimal combinatorial contracts: polynomial for gross substitutes, NP-hard for submodular

For combinatorial contract instances with binary outcome and additive costs: if the success function $f$ is gross substitutes, an optimal contract can be computed with polynomially many value queries and polynomial running time; if $f$ is submodular (even explicitly given coverage-type functions), computing an optimal contract is NP-hard. The positive result extends to linear contracts for higher-dimensional outcome spaces, which are robustly optimal given first-moment constraints.

## Proof sketch

For gross substitutes, enumerate the polynomially many critical values, compute the demanded set at each with a greedy demand oracle, and evaluate the principal's utility, taking the best. For submodular $f$, reduce from a partition-type problem: build a coverage function whose critical values encode subset sums, so that achieving a target principal utility requires the agent's demand at some $\alpha$ to correspond to an exact solution.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Gross-substitutes success-probability function](gross-substitutes-success-probability.md)

## Proof depends on

- [Gross-substitutes success functions have polynomially many critical values](gross-substitutes-polynomially-many-critical-values.md)
- [With a binary outcome, contracts paying only on success are without loss](binary-outcome-pay-on-success.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021, arXiv:2109.14260.
- T. Ezra, M. Feldman, M. Schlesinger, "On the (In)approximability of Combinatorial Contracts", ITCS 2024.
