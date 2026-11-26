# Period

The period `θ(a, α a; β z₀)` of `ρ` at `α, β : G`, for points `a` and `z₀` of the upper half
plane: the theta function with parameters `a` and `α a = pmoebius K₀ (ρ α) a`, normalized at `z₀`,
evaluated at `β z₀ = pmoebius K₀ (ρ β) z₀`. Both images are actual points of the upper half plane
(`pmoebius_mem_upperHalfPlane`). Like `theta`, it needs a Hausdorff topological ring `K`. It is the
analytic period only when `z₀` avoids the orbit of `a` (which is also the orbit of `α a`) and the
theta product converges at `β z₀`, as the source's theorem on periods assumes; the definition
requires neither. If `z₀ = γ a` for some `γ`, the `γ`-th factor is `0` and `period` is the
totalized value `0`: for the trivial group it is `1` when `a ≠ z₀` and `0` when `a = z₀`.
