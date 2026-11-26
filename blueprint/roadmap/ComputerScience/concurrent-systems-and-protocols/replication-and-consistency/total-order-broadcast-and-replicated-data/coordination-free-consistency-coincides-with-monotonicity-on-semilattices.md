# Coordination-free consistency coincides with monotonicity on semilattices

Consider a partitionable asynchronous network of replicas whose states lie in a join semilattice and are merged by joins, where each replica irrevocably emits facts computed by a query on its local state. The query admits coordination-free consistent evaluation (the facts emitted under every gossip schedule equal the query evaluated on the global join) if and only if the query is monotone with respect to the semilattice order; the same characterization holds for monotone observation. In particular, testing emptiness of a grow-only set, the elements of a two-phase set, or the exact value of a grow-only counter are not coordination-free, while threshold tests on counters and membership in grow-only sets are.

## Proof sketch

If the query is monotone, facts emitted from any local state remain valid for the global join. If not, two states $s \le s'$ with a fact true at $s$ but false at $s'$ give a schedule where a replica emits it before receiving the rest of the global state.

## Depends on

- [Monotonic semilattice objects](../monotonic-semilattice-objects.md)
- [Convergence of state-based CRDTs](../convergence-of-state-based-crdts.md)

## Sources

- Joseph M. Hellerstein, "The Declarative Imperative: Experiences and Conjectures in Distributed Logic", ACM SIGMOD Record, 2010.
- Tom J. Ameloot, Frank Neven and Jan Van den Bussche, "Relational Transducers for Declarative Networking", Proceedings of the 30th ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS 2011), 2011.
