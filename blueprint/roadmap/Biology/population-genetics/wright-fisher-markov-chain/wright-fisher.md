# Neutral Wright–Fisher transition matrix

The neutral Wright–Fisher transition matrix on `M` gene copies (Ewens 2004, ch. 3):
`P(i, j) = (M choose j) (i/M)^j (1 - i/M)^(M - j)`, the binomial law `Bin(M, i/M)` of the
number of `A` copies among `M` draws with replacement. The model needs `M ≥ 1`; for `M = 0`
(where `i / M` is Lean's junk value `0`) the matrix is the one-state chain, which is
`Bin(0, p) = δ₀` for every `p`.
