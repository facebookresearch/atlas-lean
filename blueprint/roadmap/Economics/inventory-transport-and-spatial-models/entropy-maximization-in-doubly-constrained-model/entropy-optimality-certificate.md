# Biproportional tables minimize relative entropy given margins

Entropy optimality certificate. For finite index sets and positive `K`, `a`, `b`, let
`T i j = a i * K i j * b j`. Every nonnegative table `S` with exactly the same row and column
margins as `T` satisfies `F(S) - F(T) = ∑ i j, T i j * φ(S i j / T i j) ≥ 0`, where
`F(S) = ∑ i j, S i j * log(S i j / K i j)` and `φ(x) = x log x + 1 - x`. Zero entries use the
convention `log 0 = 0` (so a zero entry contributes `0` to `F(S)` and `T i j` to the certificate
sum). Hence `T` minimizes `F` over its margin class.
