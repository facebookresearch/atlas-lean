# When an x-fast trie has no predecessor

For an x-fast trie $t$ over $w$-bit keys
and a key $x < 2^w$, the predecessor query of $x$ in $t$ returns no key if and only if
no key stored in $t$ is smaller than $x$.
