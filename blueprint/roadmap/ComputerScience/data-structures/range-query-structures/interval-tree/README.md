# Interval tree

## Interval Tree

- [Interval](interval.md)

## Interval

- [Valid interval](valid.md)
- [Boolean interval validity test](valid-2.md)
- [Overlapping closed intervals](overlaps.md)
- [Overlap test for closed intervals](overlaps-2.md)
- [Overlap test with comparison count](overlaps-with-cost.md)
- [The instrumented overlap test returns the plain result](overlaps-with-cost-fst.md)
- [Comparison count of the overlap test](overlaps-with-cost-snd.md)

## Interval Tree

- [Interval tree entry](entry.md)

## Entry

- [Search key of an interval entry](key.md)

## Interval Tree

- [Lexicographic comparison of keys](compare-key.md)
- [Operation cost counters for interval trees](cost.md)
- [Interval tree](tree.md)

## Tree

- [Cached maximum of an interval tree](cached-max.md)
- [Maximum with an optional value](max-with.md)
- [Maximum high endpoint at a node](node-max.md)
- [Node construction with repaired metadata](mk-node.md)
- [Cache invariant of an interval tree](cache-invariant.md)
- [Low-endpoint ordered interval tree](low-ordered.md)
- [Validity invariant of an interval tree](valid-invariant.md)
- [Right rotation](rotate-right.md)
- [Left rotation](rotate-left.md)
- [Left-right double rotation](rotate-left-right.md)
- [Right-left double rotation](rotate-right-left.md)
- [AVL rebalancing step with cost](rebalance-with-cost.md)
- [Keyed insertion with cost](insert-key-with-cost.md)
- [Removing the leftmost entry, with its cost](remove-min-with-cost.md)
- [Keyed erasure with cost](erase-key-with-cost.md)
- [Instrumented overlap search](search-with-cost.md)
- [Instrumented search in the empty tree](search-with-cost-empty.md)
- [Instrumented search in a one-entry tree](search-with-cost-singleton.md)
- [Interval-tree overlap search](search.md)
- [Linear-scan overlap search](oracle-search.md)
- [Completeness of interval-tree search](search-complete.md)
- [Interval-tree search fails exactly when nothing overlaps](search-eq-none-iff.md)
- [Executable cache check for interval trees](cache-ok.md)
- [Key between optional bounds](key-between.md)
- [Ordered-and-valid check for interval trees](ordered-valid.md)
- [Boolean AVL balance check for interval trees](balanced.md)
- [AVL balance of an interval tree](balanced-prop.md)
- [Key-ordered interval tree](key-ordered.md)
- [The executable ordering check implies key ordering](key-ordered-of-ordered-valid.md)
- [The executable ordering check implies low-endpoint ordering](low-ordered-of-ordered-valid.md)
- [The ordering check implies interval validity](valid-invariant-of-ordered-valid.md)
- [Removing the minimum preserves the other entries](remove-min-with-cost-entries-perm.md)
- [Entries after keyed insertion](insert-key-with-cost-entries-perm.md)
- [Keyed erasure removes exactly the entries with that key](erase-key-with-cost-entries-perm.md)
- [Strictly key-ordered trees have distinct keys](key-nodup-of-key-ordered.md)
- [The removed minimum has the least key](remove-min-with-cost-min-le.md)
- [Insertion into an interval tree preserves key ordering](key-ordered-insert-key-with-cost.md)
- [Removing the minimum from an interval tree preserves key ordering](key-ordered-remove-min-with-cost.md)
- [Deletion from an interval tree preserves key ordering](key-ordered-erase-key-with-cost.md)
- [Rebalancing an interval-tree node with exact stored height restores AVL balance](balanced-prop-rebalance-node.md)
- [Rebalancing a rebuilt interval-tree node restores AVL balance](balanced-prop-rebalance-mk-node.md)
- [Keyed insertion preserves AVL balance in an interval tree](balanced-prop-insert-key-with-cost.md)
- [Removing the minimum preserves AVL balance in an interval tree](balanced-prop-remove-min-with-cost.md)
- [Keyed deletion preserves AVL balance in an interval tree](balanced-prop-erase-key-with-cost.md)
- [Node construction preserves interval validity](valid-invariant-mk-node.md)
- [Stored intervals of a valid tree are valid](valid-invariant-mem.md)
- [Keyed insertion preserves interval validity](valid-invariant-insert-key-with-cost.md)
- [Removing the minimum preserves interval validity](valid-invariant-remove-min-with-cost.md)
- [Keyed erasure preserves interval validity](valid-invariant-erase-key-with-cost.md)

## Interval Tree

- [Indexed interval tree](indexed-interval-tree.md)

## Indexed Interval Tree

- [Insertion by identifier with cost](insert-with-cost.md)
- [Erasure by identifier with cost](erase-with-cost.md)
- [Forward identifier-index check](index-forward-ok.md)
- [Backward identifier-index check](index-backward-ok.md)
- [Representation check for the indexed interval tree](check.md)
- [Representation invariant of an indexed interval tree](invariant.md)

## Tree

- [The interval-tree smart constructor preserves the cache invariant](cache-invariant-mk-node.md)
- [The executable cache check implies the cache invariant](cache-invariant-of-cache-ok.md)
- [Right rotation preserves the interval-tree cache invariant](cache-invariant-rotate-right.md)
- [Left rotation preserves the interval-tree cache invariant](cache-invariant-rotate-left.md)
- [Left-right rotation preserves the interval-tree cache invariant](cache-invariant-rotate-left-right.md)
- [Right-left rotation preserves the interval-tree cache invariant](cache-invariant-rotate-right-left.md)
- [Rebalancing preserves the interval-tree cache invariant](cache-invariant-rebalance-with-cost.md)
- [Keyed insertion preserves the interval-tree cache invariant](cache-invariant-insert-key-with-cost.md)
- [Removing the minimum preserves the interval-tree cache invariant](cache-invariant-remove-min-with-cost.md)
- [Keyed deletion preserves the interval-tree cache invariant](cache-invariant-erase-key-with-cost.md)

## Indexed Interval Tree

- [Soundness of the invariant checker](invariant-of-check.md)
- [Soundness of indexed interval-tree search](search-sound.md)
- [Completeness of indexed interval search](search-complete-of-invariant.md)
- [Correctness of insertion into an indexed interval tree](insert-spec.md)
- [Correctness of erasure from the indexed interval tree](erase-spec.md)
