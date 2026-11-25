# One-bit swap matrix as identity minus singlet outer product

Let $P$ be the $4 \times 4$ integer permutation matrix, with rows and columns indexed by pairs of
bits, that swaps the two bits: $P_{(a, b), (c, d)} = 1$ if $c = b$ and $d = a$, and $0$ otherwise.
Then $P = I - s s^{\mathsf{T}}$, where $s$ is the [antisymmetric two-bit vector](bit-singlet.md)
$(0, 1, -1, 0)$.
