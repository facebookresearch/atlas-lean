# Every nonzero codeword has weight exactly `2^(m-1)`

For a nonzero message `a ≠ 0` in `𝔽₂^m`, the Hadamard codeword of `a` has Hamming weight exactly `2^(m-1)`: `hammingNorm (encode a) = 2 ^ (m - 1)`. Since the encoder is injective and sends $0$ to $0$, this says equally that every nonzero codeword of the Hadamard code has weight $2^{m-1}$.

Pick a coordinate `i` with `a i = 1`;
translating the position by `eᵢ` flips the codeword's value, so it pairs the positions where the
codeword is nonzero with those where it is zero.
