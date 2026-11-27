# Valid y-fast trie skeleton

A y-fast trie skeleton $t$ over $w$-bit keys, with bucket $B_r$
owned by each key $r$, is valid when its representative x-fast trie is valid, a key $r$ is stored
in the representative x-fast trie exactly when its bucket $B_r$ is nonempty, and every key $r$
stored in the representative x-fast trie lies in its own bucket $B_r$.

So the representatives are sampled from the stored keys: a representative $0$ whose bucket is
$\{1\}$ is not valid. The classical bucket ordering invariant (the keys of bucket $B_r$ lie in
the interval ending at $r$) is not required, so this is the invariant of the skeleton only.
