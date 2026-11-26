# Independence-query count of matroid intersection

Run the augmenting-path matroid intersection algorithm with one independence oracle for each matroid on $n$ distinct candidate elements. A phase starting from a common independent set $I$ makes exactly $2(n - |I|)(1 + |I|)$ independence queries (building the source, sink and exchange arcs), breadth-first search being free; since there are at most $r + 1$ phases for $r$ the size of a maximum common independent set, the total is $O(n (r + 1)^2)$.

## Depends on

- [Value and independence oracle models](value-and-independence-oracle-models.md)
- [Matroid intersection by augmenting paths](../matroid-intersection-by-augmenting-paths.md)

## Sources

- A. Schrijver, "A Course in Combinatorial Optimization", lecture notes, CWI and University of Amsterdam, 2017.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
