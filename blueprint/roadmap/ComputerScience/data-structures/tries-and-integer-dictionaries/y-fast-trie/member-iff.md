# Correctness of the y-fast trie membership query

Let $t$ be a valid grouped y-fast trie
over $w$-bit keys. Then for every key $x$, the membership query on $t$ (locate the least
representative at least $x$, then scan its group) returns true at $x$ if and only if $x$ lies in
the contents of $t$.
