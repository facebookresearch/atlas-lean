/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.HyersUlam
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
# Tests for Hyers–Ulam stability of the Cauchy equation

* For `f x = x + 1` on `ℝ` (defect `1`), the Hyers approximant is the
  identity, by uniqueness.
* For `f = 0` on `ℝ` (defect `0`), the Hyers approximant is `0`.
* For `f x = x + 2` on `ℝ` (Jensen defect `0`), the Jensen approximant is
  the identity, and `f` agrees with it up to the constant `f 0 = 2`.
* For `f = id` on `ℝ` (defect `0`), the continuous approximant is the
  identity continuous linear map.
* For `f z = z + 1` on `ℂ` (defect `1`), the Hyers approximant is the
  identity.
* Uniqueness: two additive maps within `1` of `x ↦ x + 1` are equal.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.FunctionalAnalysis.HyersUlamTests

open MathlibExt.Analysis.FunctionalAnalysis.HyersUlam

/-- For `f x = x + 1` on `ℝ`, the Hyers approximant is the identity. -/
example : ∃ A : ℝ →+ ℝ, A = AddMonoidHom.id ℝ ∧
    ∀ x, ‖(x + 1) - A x‖ ≤ 1 := by
  have hdef : ∀ x y : ℝ, ‖(x + y + 1) - (x + 1) - (y + 1)‖ ≤ 1 := by
    intro x y
    have e : (x + y + 1) - (x + 1) - (y + 1) = -1 := by ring
    rw [e]
    simp
  obtain ⟨A, hA⟩ := exists_addMonoidHom_of_additive_defect
    (f := fun x : ℝ => x + 1) (δ := 1) hdef
  have hAeq : A = AddMonoidHom.id ℝ := by
    apply eq_of_forall_norm_sub_le
      (f := fun x : ℝ => x + 1) (δ := 1) (A₁ := A) (A₂ := AddMonoidHom.id ℝ)
    · exact hA
    · intro x
      simp
  exact ⟨A, hAeq, hA⟩

/-- For `f = 0` on `ℝ`, the Hyers approximant is `0`. -/
example : ∃ A : ℝ →+ ℝ, A = 0 ∧ ∀ x, ‖(0 : ℝ) - A x‖ ≤ 0 := by
  have hdef : ∀ x y : ℝ, ‖(0 : ℝ) - 0 - 0‖ ≤ 0 := by
    intro x y
    simp
  obtain ⟨A, hA⟩ := exists_addMonoidHom_of_additive_defect
    (f := fun _ : ℝ => (0 : ℝ)) (δ := 0) hdef
  have hAeq : A = 0 := by
    apply eq_of_forall_norm_sub_le
      (f := fun _ : ℝ => (0 : ℝ)) (δ := 0) (A₁ := A) (A₂ := 0)
    · exact hA
    · intro x
      simp
  exact ⟨A, hAeq, hA⟩

/-- For `f x = x + 2` on `ℝ`, the Jensen approximant is the identity. -/
example : ∃ A : ℝ →+ ℝ, (∀ x, A x = x) ∧
    ∀ x, ‖(x + 2) - A x - 2‖ ≤ 0 := by
  have hdef : ∀ x y : ℝ,
      ‖(fun x : ℝ => x + 2) ((1 / 2 : ℝ) • (x + y)) -
        (1 / 2 : ℝ) • ((fun x : ℝ => x + 2) x + (fun x : ℝ => x + 2) y)‖ ≤ 0 := by
    intro x y
    have e : (fun x : ℝ => x + 2) ((1 / 2 : ℝ) • (x + y)) -
        (1 / 2 : ℝ) • ((fun x : ℝ => x + 2) x + (fun x : ℝ => x + 2) y) = 0 := by
      show (1 / 2 : ℝ) • (x + y) + 2 - (1 / 2 : ℝ) • ((x + 2) + (y + 2)) = 0
      simp only [smul_eq_mul]
      ring
    rw [e]
    simp
  obtain ⟨A, hA⟩ := exists_addMonoidHom_of_jensen_defect
    (f := fun x : ℝ => x + 2) (δ := 0) hdef
  refine ⟨A, fun x => ?_, fun x => ?_⟩
  · have h := hA x
    simp only [mul_zero, zero_add] at h
    have h0 : (x + 2) - A x - 2 = 0 :=
      norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    linarith
  · have h := hA x
    simp only [mul_zero, zero_add] at h
    exact h

/-- For `f = id` on `ℝ`, the continuous approximant is the identity CLM. -/
example : ∃ A : ℝ →L[ℝ] ℝ, A = ContinuousLinearMap.id ℝ ℝ ∧
    ∀ x, ‖x - A x‖ ≤ 0 := by
  have hdef : ∀ x y : ℝ, ‖(x + y) - x - y‖ ≤ (0 : ℝ) := by
    intro x y
    have e : (x + y) - x - y = 0 := by ring
    rw [e]
    simp
  have hcont : ContinuousAt (fun x : ℝ => x) 0 := continuousAt_id
  obtain ⟨A, hA⟩ := exists_continuousLinearMap_of_additive_defect_of_continuousAt
    (f := fun x : ℝ => x) (δ := 0) le_rfl hdef hcont
  have hAeq : A = ContinuousLinearMap.id ℝ ℝ := by
    refine ContinuousLinearMap.ext fun x => ?_
    have h := hA x
    change ‖x - A x‖ ≤ (0 : ℝ) at h
    have h0 : x - A x = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    show A x = x
    linarith
  refine ⟨A, hAeq, fun x => ?_⟩
  have h := hA x
  change ‖x - A x‖ ≤ (0 : ℝ) at h
  exact h

/-- For `f z = z + 1` on `ℂ`, the Hyers approximant is the identity. -/
example : ∃ A : ℂ →+ ℂ, A = AddMonoidHom.id ℂ ∧
    ∀ z, ‖(z + 1) - A z‖ ≤ 1 := by
  have hdef : ∀ z w : ℂ, ‖(z + w + 1) - (z + 1) - (w + 1)‖ ≤ 1 := by
    intro z w
    have e : (z + w + 1) - (z + 1) - (w + 1) = -1 := by ring
    rw [e]
    simp
  obtain ⟨A, hA⟩ := exists_addMonoidHom_of_additive_defect
    (f := fun z : ℂ => z + 1) (δ := 1) hdef
  have hAeq : A = AddMonoidHom.id ℂ := by
    apply eq_of_forall_norm_sub_le
      (f := fun z : ℂ => z + 1) (δ := 1) (A₁ := A) (A₂ := AddMonoidHom.id ℂ)
    · exact hA
    · intro z
      simp
  exact ⟨A, hAeq, hA⟩

/-- Uniqueness: two additive maps within `1` of `x ↦ x + 1` are equal. -/
example : ∀ {A₁ A₂ : ℝ →+ ℝ}, (∀ x, ‖(x + 1) - A₁ x‖ ≤ 1) →
    (∀ x, ‖(x + 1) - A₂ x‖ ≤ 1) → A₁ = A₂ := by
  intro A₁ A₂ h₁ h₂
  exact eq_of_forall_norm_sub_le (f := fun x : ℝ => x + 1) (δ := 1) h₁ h₂

end MathlibExtTest.Analysis.FunctionalAnalysis.HyersUlamTests
