# Transpose

The **transposition** of `s` at positions `a ≤ b ≤ c ≤ d`: with `L = s.drop (q - 1)`,
`s.take (q - 1) ++ L[0, a) ++ L[c, d) ++ L[b, c) ++ L[a, b) ++ L.drop d`.
