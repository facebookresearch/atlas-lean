# Merkle signature verification

A signature $(i, pk, s, p)$ on a message $m$ verifies against the root $r$ of a tree with $n$ leaves
when $s$ is a valid Lamport signature on $m$ under $pk$ and $p$ is a valid authentication path from
the leaf $H(pk)$ at index $i$ to $r$. Without a root, no signature verifies.
