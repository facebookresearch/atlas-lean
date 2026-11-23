# Lookup count of the instrumented Huffman loop

For every fuel $n$, next serial number $s$,
binary min-heap $H$ of Huffman priorities and table $T$ whose cells each hold at most one work
item, the Huffman loop with lookup count on $(n, s, H, T)$ fails exactly when the bounded Huffman
merge loop on $(n, s, H, T)$ fails, and returns $(t, 2n + 1)$ when the merge loop returns the tree
$t$: two indexed table reads for each of the $n$ merges and one for the final step.
