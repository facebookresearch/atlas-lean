# Discarding the lookup count recovers the Huffman loop

For every fuel $n$, next serial
number $s$, binary min-heap $H$ of Huffman priorities and table $T$ whose cells each hold at most
one work item, discarding the count from the result of the Huffman loop with lookup count on
$(n, s, H, T)$ gives the result of the bounded Huffman merge loop on $(n, s, H, T)$: the two fail
together, and otherwise they return the same tree.
