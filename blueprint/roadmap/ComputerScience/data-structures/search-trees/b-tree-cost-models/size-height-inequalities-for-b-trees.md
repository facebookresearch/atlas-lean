# Size–height inequalities for classic B-trees

A well-formed classic B-tree of minimum degree $t \ge 2$ and height $h \ge 1$ (counting nodes) with $N$ entries satisfies

$$
2 t^{h-1} - 1 \le N \le (2t)^h - 1, \qquad h \le \left\lfloor \log_t \frac{N+1}{2} \right\rfloor + 1 \quad (N \ge 1).
$$

Moreover any cost that spends at most one more than a node's key count at each node along a root-to-leaf descent is at most $2 t h$.

## Proof sketch

A non-root node has at least $t - 1$ keys and $t$ children, so level $i \ge 1$ has at least $2t^{i-1}$ nodes, giving the lower bound; each node has at most $2t - 1$ keys and $2t$ children, giving the upper bound. The cost statement sums at most $2t$ per level.

## Depends on

- [B-trees of a given minimum degree](../b-tree/is-btree.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
