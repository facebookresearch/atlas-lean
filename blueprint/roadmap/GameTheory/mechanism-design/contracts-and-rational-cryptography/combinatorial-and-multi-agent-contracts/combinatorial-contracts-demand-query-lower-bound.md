# Optimal combinatorial contracts need exponentially many demand queries for submodular rewards

Consider combinatorial contract instances with a binary outcome and a monotone success function $f$. Three different computational models give three separate results.

1. **Polynomial time with value queries (conditional).** With additive costs, submodular $f$ and only value-oracle access to $f$, no polynomial-time algorithm approximates the optimal principal utility within any constant factor, unless $\mathrm{P} = \mathrm{NP}$. This is a statement about running time; it gives no bound on the number of value queries of a computationally unbounded algorithm.
2. **Demand queries (unconditional).** With additive costs $c$ and submodular $f$, every algorithm that computes an optimal contract, with no restriction on its running time, needs exponentially many demand queries to $f$; a demand query, given an arbitrary price vector $p \in \mathbb{R}_{\ge 0}^A$, returns a set in $\arg\max_S \bigl(f(S) - \sum_{i \in S} p_i\bigr)$, with ties broken in favor of a set of larger $f(S)$. With additive costs $c$, the agent's best response to a contract $\alpha > 0$ is the answer to the special demand query $p_i = c_i/\alpha$, but the lower bound holds against queries at arbitrary prices. Symmetrically, with additive $f$ and supermodular costs $c$, computing an optimal contract needs exponentially many supply queries to $c$, where a supply query, given an arbitrary price vector $p \in \mathbb{R}_{\ge 0}^A$, returns a set in $\arg\max_S \bigl(\sum_{i \in S} p_i - c(S)\bigr)$, with ties broken in favor of a set of larger $c(S)$. These lower bounds are for exact optimization.
3. **Communication.** Now let the cost also be a set function $c : 2^A \to \mathbb{R}_{\ge 0}$, with Alice holding $f$ and Bob holding $c$. If $f$ or $c$ is additive the problem is easy, since that party can send its list of item values or costs. Every protocol that computes an optimal contract must communicate exponentially many bits, even when both parties may also make polynomially many best-response queries (each returning a set the agent demands at a given contract), when $f$ and $c$ are both submodular, both supermodular, or $f$ is submodular and $c$ supermodular ($g$ is supermodular if $g(S \cup T) + g(S \cap T) \ge g(S) + g(T)$). When $f$ and $c$ are both submodular or both supermodular, every protocol that computes any multiplicative approximation of the optimal contract must communicate $\Omega(2^n/\sqrt n)$ bits. When $f$ is supermodular and $c$ is submodular, an optimal contract is computable in polynomial time with value queries.

In contrast, for gross-substitutes $f$ and additive $c$ an optimal contract is computable with polynomially many value queries.

## Proof sketch

For item 1, it is NP-hard to distinguish a normalized unweighted coverage function with a small set of value $1$ from one in which any set of value close to $1$ is much larger; with uniform costs and one added action that only a high payment incentivizes, an approximately optimal contract would tell the two cases apart. For item 2, build equal-revenue instances: families of submodular success functions for which the principal's utility $(1 - \alpha) f(S_\alpha)$ is nearly constant across exponentially many critical values except at one hidden critical value where it is larger. A sparse-demand property ensures that each demand query reveals information about only a few critical values, so exponentially many queries are needed to find the hidden one. For item 3, a reduction from set disjointness, with the hard instance split between Alice's $f$ and Bob's $c$, and a sparse best-response property for the best-response oracle give the communication bounds.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [Gross-substitutes success-probability function](gross-substitutes-success-probability.md)
- [XOS set functions, demand queries and value queries](xos-functions-demand-and-value-queries.md)

## Proof depends on

- [Optimal combinatorial contracts: polynomial for gross substitutes, NP-hard for submodular](combinatorial-contracts-gross-substitutes-vs-submodular.md)

## Sources

- P. Dütting, M. Feldman, Y. Gal-Tzur, A. Rubinstein, "When Contracts Get Complex: Information-Theoretic Barriers", SODA 2026, arXiv:2403.09794, Table 1, Main Results 1 and 2 (Theorems 2, 4, 5, 6, 8, 10 and 11) and Appendix A.
- T. Ezra, M. Feldman, M. Schlesinger, "On the (In)approximability of Combinatorial Contracts", ITCS 2024, LIPIcs, doi:10.4230/LIPIcs.ITCS.2024.44, Section 1.1 (multi-action model, submodular success probability).
- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021, arXiv:2109.14260.
