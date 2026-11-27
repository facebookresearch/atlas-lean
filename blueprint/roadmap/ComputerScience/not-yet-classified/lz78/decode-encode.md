# LZ78 decoding inverts encoding

For every type $A$ with decidable equality and every
finite list $x$ over $A$, decoding the LZ78 encoding of $x$ returns $x$:
`LZ78.decode (LZ78.encode x) = some x`.
