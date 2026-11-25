# Maximizer of the score S1 over nonnegative edge lengths

Let `ι` and `E` be finite sets, `Q` a real `ι × ι` matrix, `B` a real `ι × E` matrix and `f ∈ ℝ^ι`.
A vector `ℓ ∈ ℝ^E` is a constrained maximizer if `ℓ e ≥ 0` for every `e` and `S1(B ℓ') ≤ S1(B ℓ)`
for every `ℓ' ∈ ℝ^E` with nonnegative entries, where `S1` is the [score](score-s1.md) with
covariance `Q` and estimated statistics `f`: the edge lengths `ℓ` maximize the score of the
predicted statistics `B ℓ` among nonnegative edge lengths. For a singular `Q` the convention that
its inverse is `0` makes `S1` identically `0`, so every nonnegative `ℓ` is a constrained maximizer;
the intended `Q` is positive definite.
