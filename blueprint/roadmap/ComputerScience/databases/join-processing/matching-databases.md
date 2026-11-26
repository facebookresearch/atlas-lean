# Matching databases

Fix a common domain $[n]=\{1,\ldots,n\}$, where $n>0$. Each relation name $i$ has a prescribed arity $r_i\ge 1$. A **matching database** assigns to each name a set of $r_i$-tuples in which every value of $[n]$ occurs in exactly one tuple at each column. Equivalently, projection onto any column is a bijection from that relation's rows to $[n]$. Thus each relation has exactly $n$ rows. Row order and repeated listings of an identical tuple do not change the set.

A unary matching contains every domain value. When $n=1$, each relation consists of the sole tuple of its arity. An empty set of names has one database, the empty assignment; this does not introduce a relation of arity zero.

## Related topics

- [Permutation representation of a matching relation](permutation-equiv.md): fixing the first column as row index determines each other column's permutation uniquely.
- [Uniform sampling of matching databases](map-independent-permutations.md): for finitely many names, independent uniform choices for all these permutations induce the uniform law on the actual databases.
- [Query hypergraph and fractional vertex covering number](query-hypergraph-and-fractional-vertex-covering-number.md)

## Sources

- P. Beame, P. Koutris and D. Suciu, *Communication Steps for Parallel Query Processing*, PODS 2013, [authors' copy, §2.5, “Input Distribution”](https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf#page=5). The paper defines the matching condition, identifies the binary case with a permutation, and specifies uniform sampling at fixed $n$. The general first-column representation and the independent sampler are derived descriptions of that law.
