# Lintegral run le geom

Assume `Measurable (fun p : S × D => f p.1 p.2)` and `Measurable V`.

The drift recursion: if one step satisfies `E V(f x d) ≤ ρ V(x) + β`, then the
expectation of `V` at mark `n` is at most `ρⁿ V(x₀) + β ∑_{k<n} ρᵏ`.
