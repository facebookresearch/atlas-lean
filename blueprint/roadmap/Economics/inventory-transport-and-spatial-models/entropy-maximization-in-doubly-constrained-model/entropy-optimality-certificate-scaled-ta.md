# The Sinkhorn-scaled table minimizes relative entropy

For an `m × n` matrix `K` with positive entries and positive vectors `a`, `b`, let
`T i j = a i * K i j * b j` be the scaled table. Every nonnegative `m × n` matrix `S` with the same
row and column margins as `T` satisfies the entropy identity
`F(S) - F(T) = ∑ i j, T i j * φ(S i j / T i j)` and the certificate sum is nonnegative,
`∑ i j, T i j * φ(S i j / T i j) ≥ 0`, where `F(S) = ∑ i j, S i j * log(S i j / K i j)`,
`φ(x) = x log x + 1 - x` and `log 0 = 0`.
