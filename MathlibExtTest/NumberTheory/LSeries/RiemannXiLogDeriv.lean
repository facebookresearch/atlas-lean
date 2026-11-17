/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.RiemannXiLogDeriv

/-!
# Tests for the bounds for `ξ'/ξ`

The good heights for `ξ'/ξ` avoid the ordinates of the zeros in absolute value and bound `ξ'/ξ`
on both horizontal lines `Im s = ±T'`.
-/

@[expose] public section

open Complex RiemannXi

namespace RiemannXiLogDerivTest

/-- Good heights on the strip `-1 ≤ σ ≤ 2`, on both lines `Im s = ±T'`. -/
example : ∃ K T₁ : ℝ, ∀ T ≥ T₁, ∃ T' : ℝ, |T' - T| ≤ 1 ∧
    (∀ ρ ∈ riemannZetaNontrivialZeros, ρ.im ≠ T' ∧ ρ.im ≠ -T') ∧
    ‖logDeriv riemannXi ((-1 : ℝ) - (T' : ℂ) * I)‖ ≤ K * Real.log T' ^ 2 := by
  obtain ⟨K, T₁, -, h⟩ := exists_good_height_norm_logDeriv_riemannXi_le one_pos
  refine ⟨K, T₁, fun T hT => ?_⟩
  obtain ⟨T', hT'1, hT'2, hz, hb⟩ := h T hT
  refine ⟨T', hT'1, fun ρ hρ => ⟨fun h => hz ρ hρ ?_, fun h => hz ρ hρ ?_⟩,
    (hb (-1) le_rfl (by norm_num)).2⟩
  · rw [h, abs_of_pos (by linarith)]
  · rw [h, abs_neg, abs_of_pos (by linarith)]

/-- `ξ'/ξ(w) = O(log |w|)` on `Re w ≥ 2`. -/
example : ∃ K : ℝ, ∀ w : ℂ, 1 + 1 ≤ w.re → ‖logDeriv riemannXi w‖ ≤ K + Real.log (‖w‖ + 1) :=
  exists_norm_logDeriv_riemannXi_le one_pos

end RiemannXiLogDerivTest
