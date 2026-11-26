/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZeckendorfRenewal

open MeasureTheory MetaMathlibExt

namespace ZeckendorfRenewalTest

variable (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
  (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)

private lemma digit_two (P : ℕ → Prop) : (∀ i, 2 ≤ i → i ≤ 2 → P i) ↔ P 2 :=
  ⟨fun h => h 2 le_rfl le_rfl, fun h _ hi hi' => le_antisymm hi' hi ▸ h⟩

private def oneDigit (i : ℕ) : Bool := decide (i = 2)

private lemma oneDigit_mem : oneDigit ∈ zeckAdic := by
  refine ⟨rfl, rfl, fun i => ?_⟩
  simp [oneDigit]
  omega

-- After 00 the first free digit is 4. After 01 (in increasing index order) it is 5.
example :
    ProbabilityTheory.cond μ {x | x 3 = false ∧ x 2 = false} {x | x 4 = true} =
      μ {x | x 2 = true} ∧
    ProbabilityTheory.cond μ {x | x 3 = true ∧ x 2 = false} {x | x 5 = true} =
      μ {x | x 2 = true} := by
  have h := zeckOdometer_invariant_measure_renewal μ hX hT (k := 2) (ℓ₀ := 2) le_rfl
    (y := fun _ => false) (by simp [zeckAdic]) oneDigit_mem
  simpa only [digit_two, oneDigit, decide_true] using And.intro h.1 (h.2 rfl)

-- The empty tail cylinder has conditional mass one even when the low digit is one.
example :
    ProbabilityTheory.cond μ {x | x 3 = false ∧ x 2 = true} Set.univ = 1 := by
  have empty_interval (P : (ℕ → Bool) → ℕ → Prop) :
      {x | ∀ i, 2 ≤ i → i ≤ 1 → P x i} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x i hi hi'
    omega
  have h := (zeckOdometer_invariant_measure_renewal μ hX hT (ℓ₀ := 1) (k := 2) le_rfl
    oneDigit_mem oneDigit_mem).1
  rw [empty_interval (fun x i => x (i + 2) = oneDigit i),
    empty_interval (fun x i => x i = oneDigit i)] at h
  simpa [digit_two, oneDigit] using h

end ZeckendorfRenewalTest
