# Public key of the Merkle signature scheme

The public key for Lamport secret keys $sk_0, \dots, sk_{N-1}$ is the Merkle root over the hashes of
their Lamport public keys. There is none when $N = 0$.
