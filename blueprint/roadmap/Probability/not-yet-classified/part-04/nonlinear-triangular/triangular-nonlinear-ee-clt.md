# Triangular-array CLT for a nonlinear cluster estimating equation

Rows of `n`
independent clusters contribute estimating functions `ψ_{n,i}(β)`, differentiable in `β` with
derivative `ψ'_{n,i}(β)`; `Ψₙ = ∑ᵢ ψ_{n,i}` (`nonlinearEE`). Assume

* (**scores at the truth**, T36) the cluster scores `ψ_{n,i}(β₀)` are independent within rows,
  measurable, mean zero, bounded by `K · m n i`, with positive row variance `Bₙ²` eventually and
  negligible largest cluster, `K Mₙ / Bₙ → 0`;
* (**root and consistency**) `β ↦ Ψₙ(β)` is antitone, `β̂ₙ` is a.e.-measurable and a root with
  probability tending to one, and for every `ε > 0`, `Ψₙ(β₀ - ε) > 0 > Ψₙ(β₀ + ε)` with
  probability tending to one (so `β̂ₙ → β₀` by `tendstoInMeasure_root_of_antitone`);
* (**linearization**) for a deterministic sensitivity `Dₙ > 0`, the slope
  `Ψ'ₙ = ∑ᵢ ψ'_{n,i}` is locally uniformly within `ε Dₙ` of `-Dₙ` with probability tending to one.

Then `Dₙ (β̂ₙ - β₀) / Bₙ ⇒ N(0, 1)`, i.e. `β̂ₙ` is asymptotically normal with sandwich variance
`Bₙ² / Dₙ²`. The normalization is `Dₙ / Bₙ`, not `√n`.
