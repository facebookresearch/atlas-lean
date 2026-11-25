# Forward invariance of the nonnegative orthant

Let `F` be locally Lipschitz with the
boundary-sign property: `0 ≤ F y i` whenever `y ≥ 0` and `y i = 0`. If `x` solves `x' = F x` on
a convex set `I` and `x t₀ ≥ 0` componentwise for some `t₀ ∈ I`, then `x t ≥ 0` componentwise
for every `t ∈ I` with `t₀ ≤ t`.

The proof applies Gronwall's inequality to `s ↦ ∑ i, min (x s i) 0 ^ 2` on `[t₀, t]`, with a
Lipschitz constant of `F` on a closed ball that contains the trajectory and its positive
part.
