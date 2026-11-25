# Keyed erasure removes exactly the entries with that key

The key of an entry is the pair
$(\ell, i) \in \mathbb{Z} \times \mathbb{N}$ of its low endpoint $\ell$ and identifier $i$; keys are
compared lexicographically. Let $T$ be an interval tree whose keys are strictly ordered (every key
in a left subtree is lexicographically below its node's key and every key in a right subtree is
above it), and let $k \in \mathbb{Z} \times \mathbb{N}$ be a key. Then the in-order list of entries
of the tree obtained by erasing $k$ from $T$ is a permutation of the in-order list of entries of $T$
with every entry of key $k$ removed.
