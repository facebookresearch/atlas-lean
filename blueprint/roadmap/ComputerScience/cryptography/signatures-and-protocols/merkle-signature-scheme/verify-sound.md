# Soundness of Merkle signature verification

If a signature $(i, pk, s, p)$ on $m$ verifies against the honest public key, then $s$ is a valid
Lamport signature on $m$ under $pk$, the index satisfies $i < N$, and either $pk$ is the honest
Lamport public key at index $i$, or $h$ has a collision, or $H$ has a collision.
