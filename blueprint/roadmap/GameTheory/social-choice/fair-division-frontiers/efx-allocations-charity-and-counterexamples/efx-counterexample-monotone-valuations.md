# EFX allocations can fail to exist for monotone valuations

For general monotone valuations, complete EFX allocations need not exist. There is an instance with three agents and eight goods in which all agents have monotone submodular valuations (in fact weighted coverage functions), identical up to a relabeling of the goods, that admits no complete EFX allocation. Furthermore, for every $n \ge 3$ and $m \ge n + 5$ there are instances with $n$ agents, $m$ goods and monotone valuations admitting no complete EFX allocation, while every instance with three agents, seven goods and monotone valuations admits one.

## Proof sketch

The submodular counterexample is a symmetric construction verified by exhausting all $3^8$ allocations, using the symmetry to reduce the case analysis. The monotone counterexamples and the seven-good existence result are obtained by encoding the existence of an EFX-free instance as a Boolean satisfiability problem over the order relations among bundle values; a satisfying assignment yields a counterexample, while unsatisfiability certifies existence, and padding arguments extend the base counterexample to larger $n$ and $m$.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [Existence of complete EFX allocations](../../existence-of-complete-efx-allocations.md)

## Proof depends on

- [EFX exists for two agents with arbitrary monotone valuations](efx-two-agents-monotone-valuations.md)

## Sources

- S. Mackenzie, M. Suzuki, "Counterexamples to EFX for Submodular and Subadditive Valuations", arXiv:2605.06451 (2026).
- H. Akrami, A. Mayorov, K. Mehlhorn, S. Srinivas, C. Weidenbach, "A Counterexample to EFX: n >= 3 Agents, m >= n + 5 Items, Monotone Valuations, via SAT-Solving", arXiv:2604.18216 (2026).
