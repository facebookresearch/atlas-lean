# IFDS problems are realizable-path reachability problems

Let $IP = (G^*, D, F, M, \cup)$ be an [IFDS problem](ifds-problems-and-the-meet-over-all-valid-paths.md) whose meet is union. Its *exploded supergraph* $G^\#_{IP} = (N^\#, E^\#)$ has nodes $N^\# = N^* \times (D \cup \{0\})$ and edges

$$E^\# = \{\langle m, d_1\rangle \to \langle n, d_2\rangle \mid (m, n) \in E^* \text{ and } (d_1, d_2) \in R_{M(m, n)}\},$$

where $R_f$ is the [representation relation](representation-relations-of-distributive-function.md) of $f$. A path in $G^\#_{IP}$ is *realizable* if the path of $G^*$ it projects to is [valid](supergraphs-and-valid-paths.md).

**Theorem.** For every node $n \in N^*$ and fact $d \in D$, $d \in \mathrm{MVP}_n$ if and only if there is a realizable path in $G^\#_{IP}$ from $\langle s_{\mathrm{main}}, 0\rangle$ to $\langle n, d\rangle$.

So the meet-over-all-valid-paths solution is found by solving a realizable-path reachability problem, in which only paths whose calls and returns match count.

## Depends on

- [IFDS problems and the meet-over-all-valid-paths solution](ifds-problems-and-the-meet-over-all-valid-paths.md)
- [Representation relations of distributive functions](representation-relations-of-distributive-function.md)
- [Supergraphs and valid paths](supergraphs-and-valid-paths.md)

## Sources

- T. Reps, S. Horwitz and M. Sagiv, "Precise interprocedural dataflow analysis via graph reachability", *Conference Record of the 22nd ACM Symposium on Principles of Programming Languages (POPL 1995)*, <https://research.cs.wisc.edu/wpis/papers/popl95.pdf>: Section 3.2, Definition 3.7 (the exploded supergraph) and Theorem 3.8.
