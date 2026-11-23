# Eigenbasis of the K80 rate matrix

Nucleotides are indexed `0 = A`, `1 = C`, `2 = G`, `3 = T`, so a substitution is a transition
(`A ↔ G`, `C ↔ T`) exactly when the two indices have the same parity. The K80 eigenbasis is the
`4 × 4` matrix `V` whose columns, with coordinates in the nucleotide order `A, C, G, T`, are the
constant vector `(1, 1, 1, 1)`, the purine/pyrimidine contrast `(1, -1, 1, -1)`, the contrast
`(1, 0, -1, 0)` within the purines and the contrast `(0, 1, 0, -1)` within the pyrimidines. For
every real `κ` they are eigenvectors of the
[K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md) with ratio `κ`,
with eigenvalues `0`, `-1`, `-(κ + 1)/2` and `-(κ + 1)/2` ([diagonalization](smul-k80-rate-eq.md)).
