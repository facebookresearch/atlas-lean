# LZ78 token indices point backwards

For every finite list $x$ and every index $i$ below
the number of tokens of its LZ78 encoding, the index of the $i$-th token (counting from $0$) is
at most $i$: it names the empty phrase or one of the $i$ phrases before it.
