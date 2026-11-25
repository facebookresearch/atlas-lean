# Matching databases

Fix $n \ge 1$ and a schema of relations of arities $r \ge 1$ over attributes with domain $[n] = \{1, \dots, n\}$.
A relation of arity $r$ is a matching if it has exactly $n$ tuples and every value of $[n]$ occurs exactly
once in each column, equivalently if it is the set $\{(i, \sigma_2(i), \dots, \sigma_r(i)) : i \in [n]\}$ for
permutations $\sigma_2, \dots, \sigma_r$ of $[n]$. A matching database assigns a matching to every
relation; the uniform distribution chooses these permutations independently and uniformly, which is the
uniform distribution on the finite, nonempty set of matching databases. Nullary relations are excluded.

## Related topics

- [Query hypergraph and fractional vertex covering number](query-hypergraph-and-fractional-vertex-covering-number.md)

## Sources

- Communication Steps for Parallel Query Processing (Beame, Koutris, Suciu, PODS 2013) — Beame, Koutris, Suciu; ACM PODS, authors' copy, Section 2.5 (input distribution). <https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf>
