/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# A dual norm lower bound controls the closed unit-ball image

Let `B : E →L[ℂ] F` be a bounded map between complex normed spaces, possibly incomplete. Suppose
every continuous functional `G ∈ F*` satisfies `‖G‖≤‖G∘B‖`.

Then the closed radius-one-half ball of `F` lies in the norm closure of the image of the closed
unit ball of `E`: `closedBall_F(0,1/2) ⊆ closure(B(closedBall_E(0,1)))`. This is an
approximation assertion and does not require surjectivity of `B`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Metric Set

namespace ContinuousLinearMap

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Target half-ball in the closed unit-ball image.** Let `E,F` be complex normed spaces,
with no completeness assumption, and `B : E →L[ℂ] F`. Assume `‖G‖≤‖G∘B‖` for every
continuous complex-linear functional `G ∈ F*`. `closedBall_F(0,1/2) ⊆ closure(B ''
closedBall_E(0,1))`, with closure in the norm topology of `F`. -/
theorem halfBall_subset_closure_image_unitBall_of_dual_lower_bound (B : E →L[ℂ] F)
    (hdual : ∀ G : StrongDual ℂ F, ‖G‖ ≤ ‖G.comp B‖) :
    closedBall (0 : F) (1 / 2 : ℝ) ⊆ closure (B '' closedBall (0 : E) 1) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  intro y hy
  by_contra hnot
  let C : Set F := closure (B '' closedBall (0 : E) 1)
  have hconvex : Convex ℝ C :=
    ((convex_closedBall (0 : E) 1).linear_image (B.toLinearMap.restrictScalars ℝ)).closure
  have hzero : (0 : F) ∈ C := subset_closure ⟨0, by simp, B.map_zero⟩
  obtain ⟨G, r, hC, hGy⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := ℂ) hconvex isClosed_closure hnot
  have hr : 0 < r := by
    have h := hC 0 hzero
    simpa only [map_zero, Complex.zero_re] using h
  let L : StrongDual ℂ E := G.comp B
  have hunit (x : E) (hx : ‖x‖ = 1) : ‖L x‖ ≤ r := by
    obtain ⟨c, hc, hphase⟩ := RCLike.exists_norm_eq_mul_self (L x)
    have hmem : c • x ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, hc, hx, one_mul]
    have hvalue := hC (B (c • x)) (subset_closure ⟨c • x, hmem, rfl⟩)
    have hreal : (G (B (c • x))).re = ‖L x‖ := by
      change (L (c • x)).re = ‖L x‖
      rw [L.map_smul, smul_eq_mul, ← hphase]
      exact Complex.ofReal_re _
    change (G (B (c • x))).re < r at hvalue
    rw [hreal] at hvalue
    exact hvalue.le
  have hL : ‖L‖ ≤ r := L.opNorm_le_of_unit_norm hr.le hunit
  have hG : ‖G‖ ≤ r := (hdual G).trans hL
  have hynorm : ‖y‖ ≤ (1 / 2 : ℝ) := mem_closedBall_zero_iff.mp hy
  have hpoint : (G y).re ≤ ‖G‖ * (1 / 2 : ℝ) :=
    (Complex.re_le_norm _).trans ((G.le_opNorm y).trans
      (mul_le_mul_of_nonneg_left hynorm (norm_nonneg G)))
  change r < (G y).re at hGy
  nlinarith [norm_nonneg G]

end

end ContinuousLinearMap
