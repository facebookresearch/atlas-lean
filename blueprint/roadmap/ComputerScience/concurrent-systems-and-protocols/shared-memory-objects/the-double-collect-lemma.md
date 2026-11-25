# The double-collect lemma

Let each of $n$ single-writer atomic registers hold a pair of a value and an unbounded sequence number that its writer increments on every write, so that sequence numbers never repeat, and let each read return both components atomically. If two successive collects (reading the registers one by one) return identical vectors, including the sequence numbers, then the returned vector equals the contents of the registers at every instant between the end of the first collect and the beginning of the second, and so any such instant is a valid linearization point for a scan.

## Depends on

- [Atomic snapshot objects](atomic-snapshot-objects.md)
- [The asynchronous shared-memory model](the-asynchronous-shared-memory-model.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
