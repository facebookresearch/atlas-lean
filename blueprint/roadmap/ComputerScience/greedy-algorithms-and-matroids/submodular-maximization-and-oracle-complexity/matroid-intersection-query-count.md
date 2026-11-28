# Independence-query count of matroid intersection

Run the augmenting-path matroid intersection algorithm with one independence oracle for each of two matroids $M_1, M_2$ on a ground set $S$ of $n$ elements, with rank functions $r_1, r_2$, and let $\bar r = \max(r_1(S), r_2(S)) \ge 1$ be the larger of the two matroid ranks of $S$. The algorithm makes $O(\bar r^2 n)$ independence queries: each exchange graph is built with $O(\bar r n)$ independence queries, breadth-first search being free, and the algorithm augments at most $\bar r$ times.

## Proof sketch

Sharper count in the common rank (derived; the cited sources do not state it): let $r$ be the size of a maximum common independent set. A phase starting from a common independent set $I$ queries, for each matroid and each $x \notin I$, whether $I + x$ is independent and, for each $y \in I$, whether $I - y + x$ is independent: exactly $2(n - |I|)(1 + |I|)$ queries, building the source, sink and exchange arcs. Each successful phase increases $|I|$ by one, so the phases start from sizes $0, 1, \ldots, r$, and the total is at most $\sum_{j=0}^{r} 2n(1 + j) \le 2n(r+1)^2$. So each phase uses $O(n(r+1))$ independence queries, there are at most $r + 1$ phases, and the algorithm makes $O(n(r+1)^2)$ independence queries. Since $r \le \bar r$, this is $O(\bar r^2 n)$ when $\bar r \ge 1$.

## Depends on

- [Value and independence oracle models](value-and-independence-oracle-models.md)
- [Matroid intersection by augmenting paths](../matroid-intersection-by-augmenting-paths.md)

## Sources

- A. Schrijver, "A Course in Combinatorial Optimization", lecture notes, CWI and University of Amsterdam, 2017.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
- M. X. Goemans, Lecture 11: "Matroid Intersection", 18.438 Advanced Combinatorial Optimization lecture notes, Massachusetts Institute of Technology, October 22, 2009, Section 4.
