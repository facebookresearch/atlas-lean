# Successor in an x-fast trie

For an x-fast trie $t$ over $w$-bit keys and a key
$x \in \{0, \dots, 2^w - 1\}$, the successor of $x$ in $t$ is the least stored key of $t$ that is
greater than $x$ when some stored key is greater than $x$; otherwise $x$ has no successor in $t$.

It is computed directly from the stored key set rather than by the classical binary search over
the levels, so no $O(\log w)$ time bound is claimed.
