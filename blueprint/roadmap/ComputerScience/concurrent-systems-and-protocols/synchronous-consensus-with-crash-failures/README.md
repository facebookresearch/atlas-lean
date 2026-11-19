# Synchronous consensus with crash failures

Consensus in synchronous rounds when processes may crash. The model on these pages: lock-step rounds in which every process sends one message to every process; crash (stopping) failures, a process crashing in some round delivering its messages of that round to an arbitrary subset of the processes and nothing afterwards; a complete network of reliable links on which a receiver knows the sender; deterministic protocols deciding after a fixed number of rounds. Consensus asks for agreement among correct processes and validity (a decided value is some process's input). Tolerating $f$ crashes needs $f + 1$ rounds when there are at least $f + 2$ processes.

- [Synchronous protocol with crash failures](crash-protocol.md)
- [Crash pattern](crash-pattern.md)
- [Message delivery under a crash pattern](delivers.md)
- [A correct process delivers every message](delivers-of-eq-none.md)
- [Faulty processes of a crash pattern](faulty.md)
- [Faulty processes are those that crash](mem-faulty.md)
- [Crash round](crash-round.md)
- [Admissible crash pattern for $T$ rounds](good.md)
- [An admissible pattern has at most $T$ faulty processes](card-faulty-le.md)
- [Executions under crash failures](state.md)
- [One round of an execution under crash failures](state-succ-eq.md)
- [Executions agree while deliveries agree](state-congr.md)
- [A silent process changes nothing for the others](state-eq-of-silent.md)
- [Decision under crash failures](decision.md)
- [Solving consensus with crash failures](solves.md)
- [Consensus needs a round](not-solves-zero.md)
- [Solving consensus against at most one crash per round](solves-one-per-round.md)
- [Consensus against $T$ crashes, at most one per round, needs more than $T$ rounds](not-solves-one-per-round.md)
- [Solving consensus against $f \ge T$ crashes includes one crash per round](solves-one-per-round-of-solves.md)
- [Consensus with $f$ crash failures needs $f + 1$ rounds](f-add-one-le-of-solves.md)

## Related topics

- [Byzantine agreement](../byzantine-agreement/README.md): the same synchronous rounds with Byzantine instead of crash failures, where the number of processes must exceed $3m$.
- [FLP impossibility](../flp-impossibility/README.md): without synchrony one crash already makes consensus impossible; the $f + 1$ bound has a bivalence proof modelled on it.
