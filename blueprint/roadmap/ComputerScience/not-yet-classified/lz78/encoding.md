# LZ78 codec

The LZ78 encoder `LZ78.encode` and decoder `LZ78.decode`, with the round trip
`LZ78.decode_encode`, as an instance of Mathlib's `Computability.Encoding` contract for finite
lists over a type $A$ with decidable equality, with LZ78 tokens as the code alphabet.
