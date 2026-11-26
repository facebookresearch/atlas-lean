# Cont Hash

The **continuation hash** `H'_z(m)`: the Merkle–Damgård chain started at the chaining value
`z` over the blocks of `m` padded as the continuation of one `n`-bit block (the length field
encodes `n + |m|`), finished with the block count of the whole message, one more than the blocks
of `m`. It is how `fullHash` finishes a message after its first block (`fullHash_vector_append`);
it is not `fullHash` started at `z`, which pads `m` alone.
