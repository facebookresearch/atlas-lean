/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpShiftOperatorSpectrum

/-!
# Tests for the unilateral shift on `ℓ²(ℕ, 𝕜)`

* The shift moves the first basis vector up one coordinate and kills
  coordinate `0` of every vector in its range.
* The backward shift is the adjoint, and `B ∘ S = 1`.
* `‖S‖ = 1`, and `S` is not surjective.
* The spectrum of `S` is the closed unit disc: it contains `0` and
  `1`, but not `2`.
* The geometric vector `(1, 1/2, 1/4, …)` is an eigenvector of `B`
  with eigenvalue `1/2`.
-/

open Set Filter Topology Metric
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
open MathlibExt.Analysis.InnerProductSpace.LpShiftOperatorSpectrum

namespace MathlibExtTest.Analysis.InnerProductSpace.LpShiftOperatorTests

/-- The shift sends `e₀` to `e₁`: coordinate `1` is `1`. -/
example : (shiftCLM (lp.single 2 0 (1 : ℂ)) : ℕ → ℂ) 1 = 1 := by
  simp [shiftCLM_apply, lp.single_apply]

/-- The shift sends `e₀` to `e₁`: coordinate `0` is `0`. -/
example : (shiftCLM (lp.single 2 0 (1 : ℂ)) : ℕ → ℂ) 0 = 0 := by
  simp [shiftCLM_apply]

/-- The shift sends `e₀` to `e₁`: coordinate `2` is `0`. -/
example : (shiftCLM (lp.single 2 0 (1 : ℂ)) : ℕ → ℂ) 2 = 0 := by
  simp [shiftCLM_apply]

/-- The backward shift sends `e₁` to `e₀`: coordinate `0` is `1`. -/
example : (backwardCLM (lp.single 2 1 (1 : ℂ)) : ℕ → ℂ) 0 = 1 := by
  simp [backwardCLM_apply, lp.single_apply]

/-- The backward shift kills `e₀`. -/
example : backwardCLM (lp.single 2 0 (1 : ℂ)) = (0 : ℓ²(ℕ, ℂ)) := by
  apply lp.ext
  funext i
  simp [backwardCLM_apply, lp.single_apply]

/-- The operator norm of the shift is `1`. -/
example : ‖shiftCLM (𝕜 := ℂ)‖ = 1 :=
  norm_shiftCLM

/-- The adjoint of the shift is the backward shift. -/
example : (shiftCLM (𝕜 := ℂ))† = backwardCLM :=
  adjoint_shiftCLM

/-- `B ∘ S = 1`. -/
example : backwardCLM ∘L shiftCLM = (1 : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) :=
  backward_comp_shift

/-- The shift is not surjective. -/
example : ¬ Function.Surjective (shiftCLM (𝕜 := ℂ)) :=
  not_surjective_shiftCLM

/-- `0` is in the spectrum of the shift. -/
example : (0 : ℂ) ∈ spectrum ℂ (shiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_shiftCLM]
  exact Metric.mem_closedBall_self zero_le_one

/-- `1` is in the spectrum of the shift. -/
example : (1 : ℂ) ∈ spectrum ℂ (shiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_shiftCLM]
  exact Metric.mem_closedBall.mpr (by simp [dist_eq_norm])

/-- `2` is not in the spectrum of the shift. -/
example : (2 : ℂ) ∉ spectrum ℂ (shiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_shiftCLM, Metric.mem_closedBall, dist_eq_norm]
  simp

/-- The spectrum of the backward shift is the closed unit disc. -/
example : spectrum ℂ (backwardCLM (𝕜 := ℂ)) = Metric.closedBall 0 1 :=
  spectrum_backwardCLM

/-- The geometric vector `(1, 1/2, 1/4, …)` is an eigenvector of `B`
with eigenvalue `1/2`. -/
example : backwardCLM (geometricVec (show ‖(1 / 2 : ℝ)‖ < 1 by
      norm_num [Real.norm_eq_abs])) =
    (1 / 2 : ℝ) • geometricVec (show ‖(1 / 2 : ℝ)‖ < 1 by
      norm_num [Real.norm_eq_abs]) :=
  backwardCLM_geometricVec _

/-- `S ∘ B` kills coordinate `0` of `e₃` and keeps coordinate `3`. -/
example : ((shiftCLM ∘L backwardCLM) (lp.single 2 3 (1 : ℂ)) : ℕ → ℂ) 0 = 0 := by
  rw [shift_comp_backward_apply]
  simp

/-- `S ∘ B` keeps coordinate `3` of `e₃`. -/
example : ((shiftCLM ∘L backwardCLM) (lp.single 2 3 (1 : ℂ)) : ℕ → ℂ) 3 = 1 := by
  rw [shift_comp_backward_apply]
  simp [lp.single_apply]

end MathlibExtTest.Analysis.InnerProductSpace.LpShiftOperatorTests
