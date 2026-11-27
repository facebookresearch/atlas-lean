# Snapshot isolation and the write-skew anomaly

This node collects a versioned model of snapshot isolation and its relation to the named anomalies.

## Expansion

A sound expansion has separate pages for:

1. **Model.** Transactions have start and commit timestamps; each transaction reads, for every item, the
   version committed most recently before its start, or its own earlier write; it commits only if no
   concurrent transaction that committed first wrote an item it also writes (first-committer-wins).
2. **Anomalies avoided.** Under this model, with the phenomena formalized as in Berenson et al., snapshot
   isolation exhibits no dirty reads, no fuzzy (non-repeatable) reads and no lost updates; the result is
   stated phenomenon by phenomenon, not as a blanket equivalence with ANSI levels.
3. **Write skew.** The versioned history $r_1[x_0]\,r_1[y_0]\,r_2[x_0]\,r_2[y_0]\,w_1[x_1]\,w_2[y_2]\,c_1\,c_2$, in
   which the concurrent transactions $T_1$ and $T_2$ both read $x$ and $y$ from the initial snapshot, is admitted
   by snapshot isolation and is not one-copy serializable: in either serial order one transaction would read the
   other's write. If each transaction alone preserves a constraint such as $x + y \ge 0$, the combined writes can
   violate it.

## Depends on

- [Operation of a schedule](../conflict-serializability/op.md)
- [Multiversion histories and one-copy serializability](remaining-clauses-of-multiversion-histories-and-one-copy-ser.md)

## Sources

- A Critique of ANSI SQL Isolation Levels (Berenson, Bernstein, Gray, Melton, O'Neil, O'Neil), SIGMOD 1995, Section 4.2 (snapshot isolation, first-committer-wins, the write-skew history H5) and Table 4 (anomalies possible under each isolation type). <https://courses.cs.duke.edu/compsci516/cps216/spring03/papers/berenson-etal-1995.pdf>
- A. Fekete, D. Liarokapis, E. O'Neil, P. O'Neil and D. Shasha, *Making snapshot isolation serializable*, ACM TODS 30(2), 2005, Section 1.1 and Definition 1.1 (p. 495). <https://cs.nyu.edu/~shasha/papers/serializablesnap>
