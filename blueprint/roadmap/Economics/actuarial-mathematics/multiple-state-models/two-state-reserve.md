# Two State Reserve

For real-valued paths `δ, μ, π, b`, maturity `T` and terminal benefit `g`, the two-state
reserve at time `t` is `V(t) = ∫ₜᵀ F(t,s)(μ(s)b(s) − π(s)) ds + F(t,T)g`, where
`F(t,s) = exp(−∫ₜˢ (δ(u) + μ(u)) du)`. Benefits are costs and premium income is subtracted.
The integrals are oriented real interval integrals. For a policy they are used on `0 ≤ t ≤ T`
with continuous paths on `[0,T]` and nonnegative interest `δ` and exit intensity `μ`.
