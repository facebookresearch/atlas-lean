# y-fast trie skeleton

A y-fast trie skeleton over $w$-bit keys consists of an x-fast trie
over $w$-bit keys, whose stored keys are the representatives, together with a bucket $B_r$, a
finite set of keys, for every key $r \in \{0, \dots, 2^w - 1\}$.

In the classical structure each bucket is a balanced search tree of $\Theta(w)$ keys; here buckets
are plain finite sets, the bucket ordering invariant and the split and merge maintenance are not
modeled, and no complexity bound is claimed.
