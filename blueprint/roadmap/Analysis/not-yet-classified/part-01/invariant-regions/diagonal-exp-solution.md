# Diagonal linear system

If `x t i = x₀ i * exp (d i * t)` for all `t` and `i`, then `x`
solves the diagonal system `x' i = d i * x i`, that is `HasDerivAt x (fun i => d i * x t i) t`
for every `t`, with `x 0 = x₀`.
