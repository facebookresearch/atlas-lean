# EFX allocations can fail to exist for monotone valuations

For general monotone valuations, complete EFX allocations need not exist. There is an instance with three agents and eight goods in which all agents have monotone submodular valuations (in fact weighted coverage functions), identical up to a relabeling of the goods, that admits no complete EFX allocation. Furthermore, for every $n \ge 3$ and $m \ge n + 5$ there are instances with $n$ agents, $m$ goods and monotone valuations admitting no complete EFX allocation, while every instance with three agents, at most seven goods and monotone valuations admits one.

## Proof sketch

The eight-good instance is invariant under every simultaneous permutation of the agents and their associated good types, and this symmetry reduces the nonexistence proof to a short case analysis; padding arguments extend the counterexample to all $n \ge 3$ and $m \ge n + 5$. The seven-good existence result comes from an analysis, valid for any number of goods, of when the invariant-based technique for three agents produces an EFX allocation. A first version of both results was found by encoding the question as a SAT/SMT problem over the order relations among bundle values, and that encoding guided the pen-and-paper proofs.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- H. Akrami, S. Mackenzie, A. Mayorov, K. Mehlhorn, S. Srinivas, M. Suzuki, C. Weidenbach, "EFX Need Not Exist", arXiv:2604.18216 (2026).
