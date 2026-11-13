# Huffman loop invariant

Let $n$ be a natural number, $H$ a binary min-heap of Huffman
priorities and $T$ an array of optional Huffman work items, and let $F$ be the list of work
items stored in $T$, in array order. The invariant holds when the multiset of elements of $H$
equals the multiset of priorities of the items of $F$; the serial numbers of the items of $F$ are
pairwise distinct; every item of $F$ has serial number less than $n$; every item of $F$ has
priority weight equal to the total leaf weight of its tree; $T$ has exactly $n$ cells; and every
item of $F$ is stored in the cell of $T$ whose index is its serial number.
