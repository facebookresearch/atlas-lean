# The double-length-encoded Merkle–Damgård hash

**The double-length-encoded Merkle–Damgård hash** of a bit string: pad with the strengthened
padding (which appends the bit length), cut into `n`-bit blocks, and apply the block-level
transform, which appends the block count as a further block. This is a strengthened variant of
Katz and Lindell's Construction 5.3, not that construction: Construction 5.3 zero-pads and appends
the bit length once.
