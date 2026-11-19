# Predecessor query in an x-fast trie

For an x-fast trie $t$ over $w$-bit keys and
a key $x < 2^w$, the predecessor of $x$ in $t$ is the greatest key stored in $t$ that is
smaller than $x$, if such a key exists; otherwise the query returns no key.
