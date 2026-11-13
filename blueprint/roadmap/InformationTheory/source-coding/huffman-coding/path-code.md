# Root-to-leaf path code

For a Huffman tree $T$ and a symbol $s$, the path code of $s$
in $T$ records the edges on the path from the root of $T$ to the leftmost leaf labelled $s$,
writing false for a left edge and true for a right edge. If $T$ is a single leaf labelled $s$,
the path code is empty; if no leaf of $T$ is labelled $s$, there is no path code.
