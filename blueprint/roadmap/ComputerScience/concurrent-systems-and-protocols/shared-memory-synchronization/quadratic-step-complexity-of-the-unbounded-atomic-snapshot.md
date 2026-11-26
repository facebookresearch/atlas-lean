# Quadratic step complexity of the unbounded atomic snapshot

In the unbounded single-writer atomic snapshot algorithm of Afek et al., in which scans repeat double collects of all $n$ registers and borrow the embedded view of a process seen to move twice, every scan or update operation completes within $2n^2 + 4n + 3$ of its own steps regardless of the other processes' behaviour, and every reachable execution is linearizable with respect to the sequential snapshot specification.

## Proof sketch

Each unsuccessful double collect observes some process move; after $n + 1$ double collects some process has moved twice, and its second update embedded a scan performed entirely within the current scan's interval, which can be returned. Each collect costs $n$ reads.

## Depends on

- [Atomic snapshot objects](../shared-memory-objects/atomic-snapshot-objects.md)
- [A wait-free atomic snapshot](../shared-memory-objects/a-wait-free-atomic-snapshot.md)

## Proof depends on

- [The double-collect lemma](../shared-memory-objects/the-double-collect-lemma.md)
- [Linearizability](../shared-memory-objects/linearizability.md)

## Sources

- Yehuda Afek et al., "Atomic Snapshots of Shared Memory", Journal of the ACM, 1993.
