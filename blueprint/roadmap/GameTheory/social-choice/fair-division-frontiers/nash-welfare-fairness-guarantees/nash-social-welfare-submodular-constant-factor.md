# Constant-factor approximation of Nash social welfare for submodular valuations

Let each agent have a monotone submodular valuation $v_i : 2^M \to \mathbb{R}_{\ge 0}$ with $v_i(\emptyset) = 0$, accessible by value queries. There is a polynomial-time algorithm using polynomially many value queries that is an $O(1)$-approximation (with constant $380$) for maximum Nash social welfare; furthermore a deterministic $(4 + \varepsilon)$-approximation is achievable in polynomial time for every fixed $\varepsilon > 0$ by combining a matching of one good per agent with local search.

## Proof sketch

First assign to each agent at most one good via a maximum-weight matching in which edge weights are logarithms of singleton values; this handles agents whose value is dominated by one good. Then improve the allocation of the remaining goods by local search, and finally recompute the matching of the matched goods given the local-search bundles; submodularity guarantees that a local optimum loses only a constant factor against any fixed allocation, and the matching step ensures the comparison allocation can be charged agent by agent.

## Depends on

- [Approximation ratio for the Nash social welfare objective](nash-social-welfare-approximation-ratio.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- W. Li, J. Vondrák, "A constant-factor approximation algorithm for Nash social welfare with submodular valuations", FOCS 2021.
- J. Garg, E. Husić, W. Li, L. A. Végh, J. Vondrák, "Approximating Nash Social Welfare by Matching and Local Search", STOC 2023, arXiv:2211.03883.
