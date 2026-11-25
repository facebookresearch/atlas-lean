# Insertion into an x-fast trie

Inserting a $w$-bit key $x$ into an x-fast trie $t$ adds $x$
to the keys stored in $t$ and, for each level $0 \le l \le w$, adds the $l$-bit prefix of $x$ to
the prefix set at level $l$.
