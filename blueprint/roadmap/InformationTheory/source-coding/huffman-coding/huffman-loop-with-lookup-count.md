# Huffman loop with lookup count

For a fuel $n$, a next serial number $s$, a binary min-heap
$H$ of Huffman priorities and a table $T$ whose cells each hold at most one work item, the Huffman
loop with lookup count on $(n, s, H, T)$ is the Huffman loop with an accumulated lookup count on
$(n, s, H, T)$ started with counter $0$. It runs the bounded sequence of Huffman merges and counts
indexed table lookups, one for each work item taken from the table: two per merge and one at the
final step. On success it returns the resulting tree together with the count; otherwise it fails.

The count excludes heap operations, table writes (emptying cells and appending merged work items)
and the final check that the table holds no work item.
