# CPA security of PRF-based encryption

Let `K`, `X` and the coins `R` be finite and nonempty, `X` with decidable
equality, and `Y` a finite additive group. For `F : K → X → Y` and an
adversary `A` making at most `q` encryption queries, the CPA advantage of `A`
against the PRF-based encryption scheme `prfEnc F` is at most the PRF
advantage against `F` of the reduction `cpaReduction q A`, plus `q / (2 |X|)`
(Katz and Lindell, Theorem 3.31).
