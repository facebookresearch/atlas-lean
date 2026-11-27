# Point, order and range queries in B+-trees

On a well-formed B+-tree, lookup, least and greatest entry, strict predecessor and successor, and rank (number of keys below a query) are correct with respect to the represented sorted map. Lookup and least and greatest entry visit one node per level; strict predecessor and successor visit at most two root-to-leaf paths (a separator need not be a stored key, so the answer may lie in the adjacent subtree); rank visits one node per level when each interior node records the entry counts of its children's subtrees. Each of these therefore visits $O(\log_t N)$ nodes. A closed-interval range query $[\ell, h]$ returns the entries with keys in $[\ell, h]$ in key order; its output is the restriction to $[\ell,h]$ of a contiguous run of leaves, in which every leaf other than the first and last is returned whole, as a chained-leaf implementation would scan it.

## Proof sketch

At each interior node the separators direct the search into the unique child that may contain the key; for predecessor and successor, the adjacent child on the search path is kept as a fallback and its extreme path is read if the first descent finds no answer; range queries descend into the children whose separator interval meets $[\ell, h]$, which form a contiguous block at each level.

## Depends on

- [B+-tree of minimum degree t](b-plus-tree.md)

## Proof depends on

- [Height of a B+-tree is logarithmic](height-of-a-b-plus-tree.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), pp. 121-137, 1979.
