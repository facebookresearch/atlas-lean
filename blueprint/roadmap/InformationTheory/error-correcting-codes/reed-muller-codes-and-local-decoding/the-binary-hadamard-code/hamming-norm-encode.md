# Every nonzero codeword has weight exactly `2^(m-1)`

For a nonzero message `a ≠ 0` in `𝔽₂^m`, the Hadamard codeword of `a` has Hamming weight exactly `2^(m-1)`: `hammingNorm (encode a) = 2 ^ (m - 1)`. Since the encoder is injective and sends $0$ to $0$, this says equally that every nonzero codeword of the Hadamard code has weight $2^{m-1}$, and, applied to $a - b$, that the codewords of distinct messages $a \ne b$ are at Hamming distance exactly $2^{m-1}$. That a nonzero linear function on $\mathbb{F}_2^m$ takes the value $1$ on exactly half of its inputs is standard; see M. Bellare, D. Coppersmith, J. Håstad, M. Kiwi and M. Sudan, [*Linearity Testing in Characteristic Two*](https://cseweb.ucsd.edu/~Mihir/papers/linearity.pdf). The pairing proof below follows the draft textbook of Guruswami, Rudra and Sudan, Proposition 2.6.3.

Pick a coordinate `i` with `a i = 1`;
translating the position by `eᵢ` flips the codeword's value, so it pairs the positions where the
codeword is nonzero with those where it is zero.
