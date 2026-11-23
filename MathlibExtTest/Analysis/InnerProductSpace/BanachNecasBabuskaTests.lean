/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.BanachNecasBabuska

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the Banach–Nečas–Babuška theorem for Hilbert spaces

* The scaled inner-product form `B x y = ⟪2 * x, y⟫` on `ℝ` satisfies the
  inf–sup condition with `β = 2` and is nondegenerate; the associated
  equivalence is multiplication by `2`, and the variational problem
  `B x y = ⟪3, y⟫` has the unique solution `x = 3 / 2`.
* The zero form fails the inf–sup condition.
* The degenerate form `B x y = x 0 * y 0` on `EuclideanSpace ℝ (Fin 2)`
  fails nondegeneracy: the second basis vector is annihilated by every `B x`.
-/

open InnerProductSpace

namespace MathlibExtTest.Analysis.InnerProductSpace.BanachNecasBabuskaTests

open MathlibExt.Analysis.InnerProductSpace.BanachNecasBabuska

/-- The scaled inner-product form `B x y = ⟪2 * x, y⟫` on `ℝ`. -/
noncomputable def testForm : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) :=
  (InnerProductSpace.toDual ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (2 • ContinuousLinearMap.id ℝ ℝ)

/-- The form `testForm` applied to `x` is the Riesz representative of `2 * x`. -/
theorem testForm_apply_clm (x : ℝ) :
    testForm x = (InnerProductSpace.toDual ℝ ℝ) (2 * x) := by
  simp [testForm]

/-- The form `testForm` in inner-product form. -/
theorem testForm_apply (x y : ℝ) : testForm x y = ⟪(2 * x : ℝ), y⟫_ℝ := by
  rw [testForm_apply_clm, InnerProductSpace.toDual_apply_apply]

/-- The dual norm of `testForm x` is `2 * ‖x‖`. -/
theorem norm_testForm_apply (x : ℝ) : ‖testForm x‖ = 2 * ‖x‖ := by
  rw [testForm_apply_clm]
  rw [LinearIsometryEquiv.norm_map]
  simp [Real.norm_eq_abs]

/-- The form `testForm` satisfies the inf–sup condition with `β = 2`. -/
theorem testForm_isInfSup : IsInfSup testForm :=
  ⟨2, two_pos, fun x => by rw [norm_testForm_apply]⟩

/-- The form `testForm` is nondegenerate. -/
theorem testForm_isNondegenerate : IsNondegenerate testForm := by
  intro y hy
  have h := hy 1
  rw [testForm_apply] at h
  simpa using h

/-- The inf–sup condition for `testForm` in classical supremum form. -/
theorem testForm_isInfSup_sup :
    ∃ β : ℝ, 0 < β ∧
      ∀ x : ℝ, β * ‖x‖ ≤ ⨆ y : {y : ℝ // ‖y‖ ≤ 1}, ‖testForm x y‖ := by
  rw [← isInfSup_iff]
  exact testForm_isInfSup

/-- The equivalence induced by `testForm` is multiplication by `2`. -/
theorem sharpEquiv_testForm (x : ℝ) :
    sharpEquiv testForm_isInfSup testForm_isNondegenerate x = 2 * x := by
  have h : sharpEquiv testForm_isInfSup testForm_isNondegenerate x =
      bilinearFormSharp testForm x := by
    simp [sharpEquiv]
  rw [h]
  simp [bilinearFormSharp, testForm_apply_clm]

/-- The equivalence `continuousLinearEquivOfBilinearForm` acts as `testForm`. -/
theorem equiv_testForm (x : ℝ) :
    continuousLinearEquivOfBilinearForm testForm_isInfSup testForm_isNondegenerate x =
      testForm x :=
  continuousLinearEquivOfBilinearForm_apply _ _ _

/-- The inverse of the equivalence induced by `testForm` has norm at most `1 / 2`. -/
theorem norm_symm_testForm :
    ‖((sharpEquiv testForm_isInfSup testForm_isNondegenerate).symm : ℝ →L[ℝ] ℝ)‖ ≤
      (2 : ℝ)⁻¹ :=
  norm_sharpEquiv_symm_le two_pos (fun x => by rw [norm_testForm_apply])
    testForm_isNondegenerate

/-- The variational problem for `testForm` has a solution with the stability bound. -/
theorem solution_testForm_exists :
    ∃ x : ℝ, (∀ y : ℝ, testForm x y = (InnerProductSpace.toDual ℝ ℝ) 3 y) ∧
      ‖x‖ ≤ (2 : ℝ)⁻¹ * ‖(InnerProductSpace.toDual ℝ ℝ) 3‖ :=
  exists_apply_eq_and_norm_le two_pos (fun x => by rw [norm_testForm_apply])
    testForm_isNondegenerate _

/-- The solution of the variational problem `B x y = ⟪3, y⟫` is `x = 3 / 2`. -/
theorem solution_testForm_value :
    (continuousLinearEquivOfBilinearForm testForm_isInfSup
      testForm_isNondegenerate).symm (InnerProductSpace.toDual ℝ ℝ 3) = 3 / 2 := by
  obtain ⟨x, hx, -⟩ := exists_unique_apply_eq testForm_isInfSup testForm_isNondegenerate
    (InnerProductSpace.toDual ℝ ℝ 3)
  have heq : (continuousLinearEquivOfBilinearForm testForm_isInfSup
      testForm_isNondegenerate) x = InnerProductSpace.toDual ℝ ℝ 3 := by
    rw [continuousLinearEquivOfBilinearForm_apply]
    apply ContinuousLinearMap.ext
    intro y
    exact hx y
  have hsymm : (continuousLinearEquivOfBilinearForm testForm_isInfSup
      testForm_isNondegenerate).symm (InnerProductSpace.toDual ℝ ℝ 3) = x := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    exact heq.symm
  rw [hsymm]
  have h1 := hx 1
  rw [testForm_apply] at h1
  have h2 : ⟪(2 * x : ℝ), (1 : ℝ)⟫_ℝ = 2 * x := by simp
  have h3 : (InnerProductSpace.toDual ℝ ℝ) 3 1 = 3 := by
    simp [InnerProductSpace.toDual_apply_apply]
  rw [h2, h3] at h1
  linarith

/-- The zero form fails the inf–sup condition. -/
theorem not_isInfSup_zero :
    ¬ IsInfSup (0 : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ)) := by
  rintro ⟨β, hβ, hB⟩
  have h := hB 1
  simp only [zero_apply, norm_zero, norm_one, mul_one] at h
  linarith

/-- The degenerate form `B x y = x 0 * y 0` on `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def degForm :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).smulRight (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)

/-- The degenerate form in coordinates. -/
theorem degForm_apply (x y : EuclideanSpace ℝ (Fin 2)) :
    degForm x y = x 0 * y 0 := by
  simp [degForm, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- The degenerate form fails nondegeneracy: the second basis vector is
annihilated by every `B x`. -/
theorem not_isNondegenerate_degForm : ¬ IsNondegenerate degForm := by
  intro h
  have h0 := h (EuclideanSpace.single 1 1) (fun x => by
    rw [degForm_apply]
    simp)
  have hne : EuclideanSpace.single (1 : Fin 2) (1 : ℝ) ≠ 0 := by
    simp [PiLp.single_eq_zero_iff]
  exact hne h0

end MathlibExtTest.Analysis.InnerProductSpace.BanachNecasBabuskaTests
