# Page-read bounds for B-tree queries

In the node-access model, minimum, maximum, lookup, membership, predecessor, successor and rank (with subtree counts) on a store denoting a well-formed B-tree of minimum degree $t$ with $N \ge 1$ entries return the same answers as the corresponding operations on the tree, using at most $\lfloor \log_t((N+1)/2) \rfloor + 1$ page reads; with a descent bound $f$ they use at most $f$ reads on every store, even a malformed one. A closed-interval range query returning $k$ entries uses at most $2(\lfloor \log_t((N+1)/2) \rfloor + 1) + k$ page reads.

## Proof sketch

Each point query reads one page per level and descends into at most one child; the height bound follows from the size–height inequalities. A range query reads the two boundary paths and, for every subtree lying entirely inside the interval, at most one page per returned entry, since every page of a well-formed tree holds at least one key.

## Depends on

- [Node-access (page-read) model for B-trees](node-access-model.md)

## Proof depends on

- [Size–height inequalities for classic B-trees](size-height-inequalities-for-b-trees.md)

## Sources

- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- A. Aggarwal and J. S. Vitter, "The Input/Output Complexity of Sorting and Related Problems", Communications of the ACM 31(9), pp. 1116-1127, 1988.
