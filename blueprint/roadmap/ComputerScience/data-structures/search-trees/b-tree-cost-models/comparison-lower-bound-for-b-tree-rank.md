# Comparison lower bound for rank search in B-trees

Let the key type be infinite and linearly ordered. Every comparison-query algorithm that computes, for every input consisting of a duplicate-free B-tree $T$ with $n$ keys and a query $q$, the rank of $q$ in $T$ (the number of keys of $T$ below $q$) must ask at least $\lceil \log_2(n + 1) \rceil$ comparisons on some input with $n$ keys. This holds already when the inputs are restricted to well-formed B-trees of any fixed minimum degree $t \ge 2$. In particular rank search with binary in-node search is optimal up to a factor $\lceil \log_2 (2t) \rceil / \log_2 t$.

## Proof sketch

Fix a tree with $n$ keys; as $q$ ranges over an infinite ordered set, all $n + 1$ ranks occur. An algorithm asking at most $d$ comparisons is a binary decision tree of depth $d$, which has at most $2^d$ leaves, so $2^d \ge n + 1$.

## Depends on

- [Comparison-query cost model](comparison-query-cost-model.md)
- [B-trees of a given minimum degree](../b-tree/is-btree.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
