# The removed minimum has the least key

Let $T$ be a key-ordered interval tree: at every
node, the keys in the left subtree are strictly smaller and those in the right subtree strictly
larger than the node's key, where the key of an entry is the pair (low endpoint, identifier)
compared lexicographically. If removing the leftmost entry of $T$ returns the entry $m$ (together
with the remaining tree and a cost record), then every entry $e$ stored in $T$ is either $m$
itself or has a key strictly larger than the key of $m$.
