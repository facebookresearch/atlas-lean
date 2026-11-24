# Call prices are convex in strike

With nonnegative state prices `ψ(ω) ≥ 0` on finitely many states, the call price
`C(K) = ∑_ω ψ(ω) max(S(ω) - K, 0)` is a convex function of the strike `K` on the whole real line.
Each summand is a nonnegative multiple of `K ↦ max(S(ω) - K, 0)`, the maximum of an affine
function and `0`; the sum of convex functions is convex.
