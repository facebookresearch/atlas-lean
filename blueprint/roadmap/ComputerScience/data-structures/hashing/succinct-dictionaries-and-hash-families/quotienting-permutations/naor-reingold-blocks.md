# Naor–Reingold blocks for small universes

On $[2^{a}]$, an unbalanced three-round Naor–Reingold block consists of a pairwise independent permutation, a Feistel round with a $k$-wise independent round function, and another pairwise independent permutation. For every $k$-tuple of distinct inputs, the output tuple of one block is within a small statistical distance $\varepsilon$ of a uniformly random $k$-tuple of distinct outputs, and composing $t$ independent blocks drives the distance down geometrically in $t$. Combined with a one-round Feistel shard router, keys of the same shard have injective suffixes, and the intra-shard $k$-tuples of buckets are close to those of a uniform permutation.

## Proof sketch

The outer pairwise independent permutations make the Feistel inputs of distinct keys collide rarely, and on non-colliding inputs the $k$-wise independent round function yields uniform outputs, as in the Luby–Rackoff analysis. Composition of independent permutations that are close to uniform on $k$-tuples contracts the statistical distance.

## Depends on

- [Universal key-quotienting permutation](../balls-to-slots-and-kick-trees/universal-key-quotienting-permutation.md)
- [Luby–Rackoff theorem](../../../../cryptography/symmetric-key/pseudorandom-constructions/lubyrackoff-theorem.md)

## Sources

- M. Naor and O. Reingold, "On the Construction of Pseudorandom Permutations: Luby-Rackoff Revisited", Journal of Cryptology 12(1), 1999.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
- M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing 17(2), 1988.
