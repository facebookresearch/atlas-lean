# B-trees on the Word RAM in O(t log_t n) instructions

There is a word-RAM implementation of classic B-trees of minimum degree $t \ge 2$ in a flat array arena in which lookup walks one root-to-leaf path in $O(t(h + 1))$ instructions, where $h$ is the height, and proactive top-down insertion (splitting a full root, then splitting every full child before descending into it) runs in $O(t h)$ instructions and allocates at most $h + 1$ nodes (one per split, plus the new root when the root splits). Both are correct with respect to the sorted association-list model, so lookup and insertion take $O(t \log_t n)$ time on $n$ keys.

## Proof sketch

Each node is a fixed-size record of $2t - 1$ key and value slots, $2t$ child pointers and a header; scanning a node costs $O(t)$ instructions and splitting a full node copies its upper half in $O(t)$ instructions. The height is logarithmic by the size–height inequalities.

## Depends on

- [B-trees of a given minimum degree](../b-tree/is-btree.md)
- [Proactive top-down splitting in B-tree insertion](proactive-top-down-splitting.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Size–height inequalities for classic B-trees](size-height-inequalities-for-b-trees.md)
- [B-tree insertion](../b-tree/insert.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
