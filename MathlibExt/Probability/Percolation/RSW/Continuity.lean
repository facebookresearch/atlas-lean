/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.RSW.OneArm

/-!
# Vanishing of a quantity dominated by a decaying one-arm bound

If `0 ≤ θ ≤ a n` for all `n` (as `θ(p) ≤ ℙ_p(0 ↔ ∂Λ_n)`) and `a n` decays geometrically over
dyadic scales or polynomially, then `θ = 0`. This is the last step of the RSW proof that there is
no infinite cluster at criticality on `ℤ²`; the decay of `a` is the hypothesis `hann` (resp.
`hpoly`).

## Main results

* `StatMech.RSW.Continuity.roc_continuity`: dyadic geometric decay of `a` gives `θ = 0`.
* `StatMech.RSW.Continuity.roc_continuity_of_polynomial`: polynomial decay of `a` gives `θ = 0`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, Chapter 11.
-/

@[expose] public section

open Filter

namespace StatMech

namespace RSW

namespace Continuity

/-- If `0 ≤ θ ≤ a n` for all `n` and `a n → 0`, then `θ = 0`. -/
theorem roc_eq_zero_of_le_tendsto {a : ℕ → ℝ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hle : ∀ n, θ ≤ a n) (hlim : Tendsto a atTop (nhds 0)) : θ = 0 := by
  refine le_antisymm ?_ hθ0
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
  exact Filter.Eventually.of_forall hle

/-- If `0 ≤ θ ≤ a n` for all `n` and `a n ≤ (1 - c) ^ ⌊log₂ n⌋` for `n ≥ 1`, then `θ = 0`. -/
theorem roc_continuity (a : ℕ → ℝ) {θ c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hθ0 : 0 ≤ θ) (hθle : ∀ n, θ ≤ a n) (hnn : ∀ n, 0 ≤ a n)
    (hann : ∀ n, 1 ≤ n → a n ≤ (1 - c) ^ (Nat.log 2 n)) :
    θ = 0 :=
  roc_eq_zero_of_le_tendsto hθ0 hθle
    (OneArm.roa_one_arm_tendsto_zero a hc0 hc1 hnn hann)

/-- If `0 ≤ θ ≤ a n` for all `n` and `a n ≤ C n ^ (-ε)` for `n ≥ 1`, then `θ = 0`. -/
theorem roc_continuity_of_polynomial (a : ℕ → ℝ) {θ ε C : ℝ} (hε : 0 < ε)
    (hθ0 : 0 ≤ θ) (hθle : ∀ n, θ ≤ a n)
    (hpoly : ∀ n, 1 ≤ n → a n ≤ C * (n : ℝ) ^ (-ε)) :
    θ = 0 := by
  have hlimC : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-ε)) atTop (nhds 0) :=
    OneArm.roa_polynomial_tendsto_zero (C := C) hε
  refine le_antisymm ?_ hθ0
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hlimC ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (hθle n).trans (hpoly n hn)

end Continuity

end RSW

end StatMech
