# Quadratic step complexity of the unbounded atomic snapshot

In the unbounded single-writer atomic snapshot algorithm of Afek et al., in which scans repeat double collects of all $n$ registers and borrow the embedded view of a process seen to move twice, every scan or update operation completes within $O(n^2)$ of its own steps regardless of the other processes' behaviour (Afek et al., Lemma 3.4), and every reachable execution is linearizable with respect to the sequential snapshot specification (Afek et al., Theorem 1).

## Proof sketch

Each unsuccessful double collect observes some process move; after $n + 1$ double collects some process has moved twice, and its second update embedded a scan performed entirely within the current scan's interval, which can be returned. Each collect costs $n$ reads.

## Depends on

- [Atomic snapshot objects](../atomic-snapshot-objects.md)
- [A wait-free atomic snapshot](../a-wait-free-atomic-snapshot.md)

## Proof depends on

- [The double-collect lemma](../the-double-collect-lemma.md)
- [Linearizability](../linearizability.md)

## Sources

- Yehuda Afek et al., "Atomic Snapshots of Shared Memory", Journal of the ACM, 1993, Lemma 3.4 and Theorem 1.
