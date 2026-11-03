/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.StrangLemma

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Strang's first lemma

Concrete one-dimensional checks of `strang_first_lemma` and
`strang_first_lemma_iInf` with the exact form `B x y = 2 * x * y`, the
perturbed form `Bh x y = 3 * x * y`, the exact functional `ℓ x = 4 * x`
and the perturbed functional `ℓh x = 5 * x`, so the exact solution is
`u = 2` and the discrete solution is `uh = 5 / 3`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.StrangLemmaTests

open MathlibExt.Analysis.InnerProductSpace.StrangLemma

/-- The bilinear form `(x, y) ↦ c * x * y` on `ℝ`. -/
private noncomputable def bilin (c : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRight (c • ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.id ℝ ℝ)

private theorem bilin_apply (c x y : ℝ) : bilin c x y = c * x * y := by
  simp [bilin, ContinuousLinearMap.smulRight_apply]

/-- The linear functional `x ↦ c * x` on `ℝ`. -/
private noncomputable def lin (c : ℝ) : ℝ →L[ℝ] ℝ :=
  c • ContinuousLinearMap.id ℝ ℝ

private theorem lin_apply (c x : ℝ) : lin c x = c * x := by
  simp [lin]

/-- The identity linear isometry on `ℝ`. -/
private noncomputable def testIsometry : ℝ →ₗᵢ[ℝ] ℝ :=
  ⟨LinearMap.id, fun x => by simp⟩

private theorem testIsometry_apply (x : ℝ) : testIsometry x = x := rfl

/-- The sign-flip linear isometry `x ↦ -x` on `ℝ`. -/
private noncomputable def negIsometry : ℝ →ₗᵢ[ℝ] ℝ :=
  ⟨-LinearMap.id, fun x => by simp⟩

private theorem negIsometry_apply (x : ℝ) : negIsometry x = -x := rfl

private theorem norm_bilin (c : ℝ) : ‖bilin c‖ = |c| := by
  simp only [bilin, ContinuousLinearMap.norm_smulRight_apply, norm_smul,
    ContinuousLinearMap.norm_id, Real.norm_eq_abs, mul_one]

private theorem norm_lin (c : ℝ) : ‖lin c‖ = |c| := by
  simp only [lin, norm_smul, ContinuousLinearMap.norm_id, Real.norm_eq_abs, mul_one]

private theorem bilin_sub (a b : ℝ) : bilin a - bilin b = bilin (a - b) := by
  ext
  simp only [sub_apply, bilin_apply]
  ring

private theorem lin_sub (a b : ℝ) : lin a - lin b = lin (a - b) := by
  ext
  simp only [sub_apply, lin_apply]
  ring

private theorem bilinearComp_bilin_testIsometry (c : ℝ) :
    (bilin c).bilinearComp testIsometry.toContinuousLinearMap
      testIsometry.toContinuousLinearMap = bilin c := by
  ext
  simp only [ContinuousLinearMap.bilinearComp_apply,
    LinearIsometry.coe_toContinuousLinearMap, testIsometry_apply, bilin_apply]

private theorem comp_lin_testIsometry (c : ℝ) :
    (lin c).comp testIsometry.toContinuousLinearMap = lin c := by
  ext
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, testIsometry_apply, lin_apply]

private theorem bilinearComp_bilin_neg (c : ℝ) :
    (bilin c).bilinearComp negIsometry.toContinuousLinearMap
      negIsometry.toContinuousLinearMap = bilin c := by
  ext
  simp only [ContinuousLinearMap.bilinearComp_apply,
    LinearIsometry.coe_toContinuousLinearMap, negIsometry_apply, bilin_apply]
  ring

private theorem comp_lin_neg (c : ℝ) :
    (lin c).comp negIsometry.toContinuousLinearMap = lin (-c) := by
  ext
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, negIsometry_apply, lin_apply]
  ring

/-- Coercivity of `Bh x y = 3 * x * y` with constant `3`. -/
private theorem coercive_bilin_three :
    ∀ v : ℝ, (3 : ℝ) * ‖v‖ * ‖v‖ ≤ bilin 3 v v := by
  intro v
  have h : ‖v‖ * ‖v‖ = v * v := by
    rw [Real.norm_eq_abs, abs_mul_abs_self]
  rw [bilin_apply]
  linarith [h]

/-- The exact equation `B 2 w = ℓ w`. -/
private theorem exact_eq : ∀ w : ℝ, bilin 2 (2 : ℝ) w = lin 4 w := by
  intro w
  rw [bilin_apply, lin_apply]
  ring

/-- The discrete equation `Bh (5 / 3) w = ℓh w`. -/
private theorem discrete_eq : ∀ w : ℝ, bilin 3 (5 / 3 : ℝ) w = lin 5 w := by
  intro w
  rw [bilin_apply, lin_apply]
  ring

/-- Perturbed one-dimensional example: `u = 2`, `uh = 5 / 3`, and the
Strang bound with the competitor `vh = 2` is `|2 - 5 / 3| ≤ 1`. -/
example : |(2 : ℝ) - 5 / 3| ≤ 1 := by
  have h := strang_first_lemma (B := bilin 2) (Bh := bilin 3) (ℓ := lin 4) (ℓh := lin 5)
    (J := testIsometry) (α := 3) (by norm_num) coercive_bilin_three exact_eq discrete_eq
    (2 : ℝ)
  simp only [bilinearComp_bilin_testIsometry, bilin_sub, comp_lin_testIsometry, lin_sub,
    norm_bilin, norm_lin, testIsometry_apply] at h
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  norm_num

/-- The infimum form on the same data: the best-approximation error
`⨅ vh, ‖2 - vh‖` is `0`, so the bound is again `|2 - 5 / 3| ≤ 1`. -/
example : |(2 : ℝ) - 5 / 3| ≤ 1 := by
  have h := strang_first_lemma_iInf (B := bilin 2) (Bh := bilin 3) (ℓ := lin 4)
    (ℓh := lin 5) (J := testIsometry) (α := 3) (by norm_num) coercive_bilin_three exact_eq
    discrete_eq
  have hiInf : (⨅ vh : ℝ, ‖(2 : ℝ) - vh‖) = 0 := by
    apply le_antisymm
    · have hbdd : BddBelow (Set.range fun vh : ℝ => ‖(2 : ℝ) - vh‖) := by
        refine ⟨0, ?_⟩
        intro y hy
        obtain ⟨vh, rfl⟩ := hy
        exact norm_nonneg _
      have hle := ciInf_le hbdd (2 : ℝ)
      rwa [sub_self, norm_zero] at hle
    · exact le_ciInf fun vh => norm_nonneg _
  simp only [bilinearComp_bilin_testIsometry, bilin_sub, comp_lin_testIsometry, lin_sub,
    norm_bilin, norm_lin, testIsometry_apply, hiInf] at h
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  norm_num

/-- The same data with the sign-flip embedding `J x = -x`: the exact
solution `2` is seen at `-2` in the discrete space, the functional crime is
`‖lin 5 - lin (-4)‖ = 9`, and the Strang bound is `|2 - -(5 / 3)| ≤ 35 / 3`. -/
example : |(2 : ℝ) - -(5 / 3 : ℝ)| ≤ 35 / 3 := by
  have h := strang_first_lemma (B := bilin 2) (Bh := bilin 3) (ℓ := lin 4) (ℓh := lin 5)
    (J := negIsometry) (α := 3) (by norm_num) coercive_bilin_three exact_eq discrete_eq
    (2 : ℝ)
  simp only [bilinearComp_bilin_neg, bilin_sub, comp_lin_neg, lin_sub,
    norm_bilin, norm_lin, negIsometry_apply] at h
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  norm_num

/-- The same data with competitor `vh = 0`: the approximation error is
`‖2 - 0‖ = 2`, and the Strang bound is `|2 - 5 / 3| ≤ 5`. -/
example : |(2 : ℝ) - 5 / 3| ≤ 5 := by
  have h := strang_first_lemma (B := bilin 2) (Bh := bilin 3) (ℓ := lin 4) (ℓh := lin 5)
    (J := testIsometry) (α := 3) (by norm_num) coercive_bilin_three exact_eq discrete_eq
    (0 : ℝ)
  simp only [bilinearComp_bilin_testIsometry, bilin_sub, comp_lin_testIsometry, lin_sub,
    norm_bilin, norm_lin, testIsometry_apply] at h
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  norm_num

end MathlibExt.Analysis.InnerProductSpace.StrangLemmaTests
