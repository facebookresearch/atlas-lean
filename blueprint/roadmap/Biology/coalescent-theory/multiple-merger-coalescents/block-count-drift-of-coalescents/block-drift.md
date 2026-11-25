# Block-count drift of a Λ-coalescent

For a finite measure `Λ` on `[0, 1]` and a natural number `b`, the **block-count drift** of the
Λ-coalescent is `γ_b = ∑_{k=2}^b (k - 1) C(b, k) λ_{b,k}`, where `λ_{b,k}` is the
[merger rate](../../coalescents/merger-rate.md): a `k`-merger among `b` blocks lowers the block
count by `k - 1` and happens at rate `C(b, k) λ_{b,k}`, so `γ_b` is the rate at which the number
of blocks is expected to decrease from `b` blocks (Schweinsberg 2000). For `b < 2` the sum is
empty and `γ_b = 0`.
