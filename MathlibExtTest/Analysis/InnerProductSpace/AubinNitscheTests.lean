/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.AubinNitsche

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the Aubin–Nitsche lemma

Concrete one-dimensional checks with the exact form
`B x y = 2 * x * y`, the weak-space map `J x = 2 * x` (so `J` is
not the identity), the error `e = 3`, and the discrete space
`Vh = ⊥` (so `uh = 0`). The adjoint solution is `z = 6`, since
`B v 6 = 12 * v = ⟪J 3, J v⟫ = ⟪6, 2 * v⟫`. Every bound below is
tight: the pointwise bound is `36 ≤ 36`, the stability bound is
`12 ≤ 12`, and the rate bound is `α * ‖J e‖ = 12 ≤
‖B‖ * ‖J‖ * 1 * 1 * ‖e‖ = 2 * 2 * 1 * 1 * 3 = 12`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.AubinNitscheTests

open MathlibExt.Analysis.InnerProductSpace.AubinNitsche

open scoped _root_.InnerProductSpace

/-- The bilinear form `(x, y) ↦ c * x * y` on `ℝ`. -/
private noncomputable def bilin (c : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRight (c • ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.id ℝ ℝ)

private theorem bilin_apply (c x y : ℝ) : bilin c x y = c * x * y := by
  simp [bilin, ContinuousLinearMap.smulRight_apply]

private theorem norm_bilin (c : ℝ) : ‖bilin c‖ = |c| := by
  simp only [bilin, ContinuousLinearMap.norm_smulRight_apply, norm_smul,
    ContinuousLinearMap.norm_id, Real.norm_eq_abs, mul_one]

/-- The scaling map `x ↦ c * x` on `ℝ`, used as the weak-space map `J`. -/
private noncomputable def scale (c : ℝ) : ℝ →L[ℝ] ℝ :=
  c • ContinuousLinearMap.id ℝ ℝ

private theorem scale_apply (c x : ℝ) : scale c x = c * x := by
  simp [scale]

private theorem norm_scale (c : ℝ) : ‖scale c‖ = |c| := by
  simp only [scale, norm_smul, ContinuousLinearMap.norm_id, Real.norm_eq_abs, mul_one]

/-- The real inner product is multiplication. -/
private theorem real_inner_mul (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  simp [RCLike.inner_apply]
  ring

/-- Coercivity of `B x y = 2 * x * y` with constant `2`. -/
private theorem coercive_bilin_two :
    ∀ v : ℝ, (2 : ℝ) * ‖v‖ * ‖v‖ ≤ bilin 2 v v := by
  intro v
  have h : ‖v‖ * ‖v‖ = v * v := by
    rw [Real.norm_eq_abs, abs_mul_abs_self]
  rw [bilin_apply]
  linarith [h]

/-- Coercivity of `B x y = 2 * x * y` as `IsCoercive`. -/
private theorem coercive_bilin_two_isCoercive : IsCoercive (bilin 2) :=
  ⟨2, by norm_num, coercive_bilin_two⟩

/-- Galerkin orthogonality for `e = 3` against `Vh = ⊥`. -/
private theorem orth_bot : ∀ wh ∈ (⊥ : Submodule ℝ ℝ), bilin 2 (3 : ℝ) wh = 0 := by
  intro wh hwh
  rw [Submodule.mem_bot] at hwh
  rw [hwh]
  simp [bilin_apply]

/-- The adjoint equation for `e = 3`, `z = 6`, `J x = 2 * x`. -/
private theorem adj_eq : ∀ v : ℝ,
    bilin 2 v (6 : ℝ) = ⟪scale 2 (3 : ℝ), scale 2 v⟫_ℝ := by
  intro v
  rw [bilin_apply, scale_apply, scale_apply, real_inner_mul]
  ring

/-- The adjoint solution given by `exists_adjointSolution` is `z = 6`. -/
example :
    ∃ z : ℝ, (∀ v : ℝ, bilin 2 v z = ⟪scale 2 (3 : ℝ), scale 2 v⟫_ℝ)
      ∧ z = 6 := by
  obtain ⟨z, hz⟩ := exists_adjointSolution (B := bilin 2) (J := scale 2)
    coercive_bilin_two_isCoercive (3 : ℝ)
  refine ⟨z, hz, ?_⟩
  have h1 := hz 1
  rw [bilin_apply, scale_apply, scale_apply, real_inner_mul] at h1
  linarith

/-- The pointwise Aubin–Nitsche bound, tight: `‖J 3‖² = 36 =
‖B‖ * ‖3‖ * ‖6 - 0‖ = 2 * 3 * 6`. -/
example :
    ‖scale 2 (3 : ℝ)‖ ^ 2 ≤ ‖bilin 2‖ * ‖(3 : ℝ)‖ * ‖(6 : ℝ) - (0 : ℝ)‖ :=
  aubinNitsche_pointwise (Vh := (⊥ : Submodule ℝ ℝ)) (Submodule.zero_mem ⊥)
    orth_bot adj_eq

/-- The infimum-form Aubin–Nitsche bound with `Vh = ⊥`. -/
example :
    ‖scale 2 (3 : ℝ)‖ ^ 2 ≤ ‖bilin 2‖ * ‖(3 : ℝ)‖
      * Metric.infDist (6 : ℝ) ((⊥ : Submodule ℝ ℝ) : Set ℝ) :=
  aubinNitsche_core (Vh := (⊥ : Submodule ℝ ℝ)) orth_bot adj_eq

/-- Adjoint stability, tight: `α * ‖z‖ = 2 * 6 = 12 =
‖J‖ * ‖J e‖ = 2 * 6`. -/
example :
    (2 : ℝ) * ‖(6 : ℝ)‖ ≤ ‖scale 2‖ * ‖scale 2 (3 : ℝ)‖ :=
  adjointSolution_norm_le (α := 2) (Cemb := ‖scale 2‖)
    coercive_bilin_two le_rfl adj_eq

/-- The rate-form Aubin–Nitsche bound, tight: `α * ‖J e‖ = 12 =
‖B‖ * ‖J‖ * 1 * 1 * ‖e‖ = 2 * 2 * 1 * 1 * 3`. The adjoint solution
`z = 6` is approximable in `⊥` by `zh = 0` with `Capp = h = 1`. -/
example :
    (2 : ℝ) * ‖scale 2 (3 : ℝ)‖ ≤ ‖bilin 2‖ * ‖scale 2‖ * 1 * 1 * ‖(3 : ℝ)‖ := by
  apply aubinNitsche_rate (α := 2) (Cemb := ‖scale 2‖) (Capp := 1) (h := 1)
    (by norm_num) coercive_bilin_two le_rfl (norm_nonneg _) (by norm_num)
    (by norm_num) orth_bot adj_eq
  exact ⟨0, Submodule.zero_mem ⊥, by norm_num⟩

/-- The trivial discrete space `Vh = ⊤`: the error is `0` and the
core bound holds with `e = z = 0`. -/
example :
    ‖scale 2 (0 : ℝ)‖ ^ 2 ≤ ‖bilin 2‖ * ‖(0 : ℝ)‖
      * Metric.infDist (0 : ℝ) ((⊤ : Submodule ℝ ℝ) : Set ℝ) := by
  apply aubinNitsche_core (Vh := (⊤ : Submodule ℝ ℝ))
  · intro wh _
    simp
  · intro v
    rw [bilin_apply, scale_apply, scale_apply, real_inner_mul]
    simp

end MathlibExt.Analysis.InnerProductSpace.AubinNitscheTests
