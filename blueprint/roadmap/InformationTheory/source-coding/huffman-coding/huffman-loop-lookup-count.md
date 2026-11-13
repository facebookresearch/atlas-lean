# Indexed reads of a successful Huffman loop

Let $k$ be a merge budget, $n$ a next serial
number, $h$ a binary min-heap of Huffman priorities and $t$ a serial-indexed table of optional
Huffman work items. If the Huffman loop with budget $k$ on $n$, $h$ and $t$ returns a tree $T$,
then the Huffman loop with lookup counting on the same arguments returns $T$ together with the
count $2k + 1$ of indexed payload-table reads.
