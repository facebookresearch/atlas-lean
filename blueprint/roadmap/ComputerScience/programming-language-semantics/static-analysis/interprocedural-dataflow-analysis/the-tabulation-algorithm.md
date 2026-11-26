# The tabulation algorithm

For an [IFDS problem](ifds-problems-and-the-meet-over-all-valid-paths.md) with union as meet, the *tabulation algorithm* solves the [realizable-path reachability problem](ifds-problems-are-realizable-path-reachability.md) on the exploded supergraph by a worklist computation of *path edges*, which summarize same-level realizable paths from the start node of a procedure to a node of that procedure, and of *summary edges*, which summarize the effect of a call from a call node to its return-site node.

1. **Correctness.** The tabulation algorithm always terminates, and on termination the set $X_n$ it computes for each node $n$ equals $\mathrm{MVP}_n$.
2. **Cost.** Assume that membership tests and insertions on the sets of path edges and summary edges take constant time, as with a bit-vector or hash representation. With $E$ the number of edges of the supergraph, $D$ the number of facts and $\mathrm{Call}$ the number of call nodes, the algorithm runs in time $O(E D^3)$ on all distributive problems and in time $O(E D^2)$ on intraprocedural ones. On *$h$-sparse* problems, in which the representation relation of every function on an ordinary intraprocedural edge or call-to-return-site edge has at most $hD$ edges leaving non-$0$ nodes, it runs in time $O(\mathrm{Call}\,D^3 + h E D^2)$, and in time $O(h E D)$ on intraprocedural ones. On locally separable problems, the gen/kill problems among them, it runs in time $O(E D)$. Its storage is bounded by $O(E D^2)$ for the exploded supergraph and $O(N D^2)$ for path edges, where $N$ is the number of nodes of the supergraph.

## Depends on

- [IFDS problems are realizable-path reachability problems](ifds-problems-are-realizable-path-reachability.md)
- [IFDS problems and the meet-over-all-valid-paths solution](ifds-problems-and-the-meet-over-all-valid-paths.md)

## Sources

- T. Reps, S. Horwitz and M. Sagiv, "Precise interprocedural dataflow analysis via graph reachability", *Conference Record of the 22nd ACM Symposium on Principles of Programming Languages (POPL 1995)*, <https://research.cs.wisc.edu/wpis/papers/popl95.pdf>: Section 4 (the tabulation algorithm and Theorem 4.1, its correctness), Section 5 (Definition 5.1 of $h$-sparse problems, Table 5.2 of running times, and the storage bounds) and the Appendix (the running-time analysis for distributive problems).
