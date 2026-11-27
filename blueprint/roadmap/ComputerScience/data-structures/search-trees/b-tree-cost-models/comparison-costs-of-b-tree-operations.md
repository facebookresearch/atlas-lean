# Comparison costs of B-tree operations

On a well-formed classic B-tree of minimum degree $t$ and height $h$, under any comparison oracle:

1. lookup, membership, minimum, maximum, predecessor, successor and rank with linear in-node scan, and insertion and deletion (including removal of the least or greatest entry), each make at most $2 t h$ comparisons, which is $O(t \log_t N)$;
2. with binary search inside each node, rank makes at most $\lceil \log_2(2t) \rceil$ comparisons per node and lookup one more, i.e. $O(\log_2 N)$ comparisons in total;
3. a closed-interval range query returning $k$ entries makes at most $4 t h + 2k$ comparisons.

Splits, merges, borrowing and root changes make no comparisons.

## Proof sketch

Each operation compares keys only while scanning the nodes of one search path (two paths for range queries); scanning a node with $r$ keys stops after at most $r + 1$ comparisons. For range queries, entries strictly inside the interval are charged two comparisons each and the remaining comparisons to the two boundary paths. Binary search over $r$ keys uses $\lceil \log_2 (r + 1) \rceil$ comparisons.

## Depends on

- [Comparison-query cost model](comparison-query-cost-model.md)
- [B-trees of a given minimum degree](../b-tree/is-btree.md)

## Proof depends on

- [Size–height inequalities for classic B-trees](size-height-inequalities-for-b-trees.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
