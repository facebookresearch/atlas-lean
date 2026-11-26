# Keys of a y-fast trie

Let $t$ be a y-fast trie over $w$-bit keys, let $R$ be the set of
keys stored in the representative x-fast trie of $t$, and for each $r \in R$ let $B(r)$ be the
bucket owned by $r$. The set of keys stored in $t$ is the union of the buckets of its
representatives, $\bigcup_{r \in R} B(r)$.

It is computed from the representatives alone, not by filtering all $2^w$ possible keys.
