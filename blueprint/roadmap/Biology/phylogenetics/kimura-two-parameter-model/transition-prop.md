# Proportion of transition differences

Nucleotides are indexed `0 = A`, `1 = C`, `2 = G`, `3 = T`, so a substitution is a transition
(`A ↔ G`, `C ↔ T`) exactly when the two indices have the same parity. For a real `4 × 4` matrix `M`
and a nucleotide `i`, the transition proportion `P(M, i)` is the entry `M i j` for the base `j ≠ i`
of the same class, purine or pyrimidine (the other index of the same parity): Kimura's `P` in row
`i`.
