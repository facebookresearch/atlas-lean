# Membership query in an x-fast trie

For an x-fast trie $t$ over $w$-bit keys
and a key $x < 2^w$, the membership query of $x$ in $t$ answers true exactly when the
length-$w$ prefix of $x$, which is $x$ itself, lies in the prefix set that $t$ stores
for level $w$: a single probe of the deepest level, as in the classical structure.
