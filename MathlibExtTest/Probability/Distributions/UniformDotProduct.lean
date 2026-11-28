/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.UniformDotProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Tests for finite-field dot product uniformity
-/

open MeasureTheory MetaMathlibExt
open scoped ENNReal

namespace MathlibExtTest.Probability.Distributions.UniformDotProduct

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem binary_zero_mass :
    Measure.uniformOfFinset (Finset.univ : Finset (Fin 2 → ZMod 2))
      {r | r ⬝ᵥ (fun _ ↦ (1 : ZMod 2)) = 0} = (2 : ℝ≥0∞)⁻¹ := by
  simpa [ZMod.card] using uniformOfFinset_dotProduct_eq
    (d := fun _ : Fin 2 ↦ (1 : ZMod 2)) (i₀ := 0) one_ne_zero 0

-- The only nonzero weight is `2` at the second coordinate.
private def weightsFive (i : Fin 2) : ZMod 5 := if i = 1 then 2 else 0

private theorem five_fiber_count (t : ZMod 5) :
    Nat.card {r : Fin 2 → ZMod 5 // r ⬝ᵥ weightsFive = t} = 5 := by
  simpa [ZMod.card] using card_dotProduct_fiber (i₀ := 1) (by decide : weightsFive 1 ≠ 0) t

private theorem five_law :
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin 2 → ZMod 5))).map
      (fun r ↦ r ⬝ᵥ weightsFive) = Measure.uniformOfFinset (Finset.univ : Finset (ZMod 5)) :=
  map_uniformOfFinset_dotProduct (i₀ := 1) (by decide)

private theorem five_nonzero_target_mass :
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin 2 → ZMod 5))).map
      (fun r ↦ r ⬝ᵥ weightsFive) {3} = (5 : ℝ≥0∞)⁻¹ := by
  rw [five_law, Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ _)]
  simp [ZMod.card]

private theorem one_coordinate_fiber :
    Nat.card {r : Fin 1 → ZMod 5 // r ⬝ᵥ (fun _ ↦ (2 : ZMod 5)) = 3} = 1 := by
  simpa using card_dotProduct_fiber (d := fun _ : Fin 1 ↦ (2 : ZMod 5)) (i₀ := 0)
    (by decide) 3

-- For this pivot the retained coordinate contributes `2 * 1`, so the inverse must
-- subtract it before dividing by the pivot weight `2`.
private def fiberWeights (i : Fin 2) : ZMod 5 := if i = 1 then 2 else 1

private noncomputable def fiveFiberEquiv :
    {r : Fin 2 → ZMod 5 // r ⬝ᵥ fiberWeights = 3} ≃ ({i : Fin 2 // i ≠ 1} → ZMod 5) :=
  dotProductFiberEquiv (by decide : fiberWeights 1 ≠ 0) 3

private theorem five_fiber_forward :
    fiveFiberEquiv ⟨fun i ↦ if i = 1 then 3 else 2, by decide⟩ ⟨0, by decide⟩ = 2 := rfl

private theorem five_fiber_inverse :
    (fiveFiberEquiv.symm (fun _ ↦ 2)).1 0 = 2 ∧ (fiveFiberEquiv.symm (fun _ ↦ 2)).1 1 = 3 := by
  constructor
  · simp [fiveFiberEquiv, dotProductFiberEquiv, show (0 : Fin 2) ≠ 1 by decide]
  · simp [fiveFiberEquiv, dotProductFiberEquiv]
    rw [Finset.sum_eq_single (⟨0, by decide⟩ : {i : Fin 2 // i ≠ 1})]
    · change (3 - 2 * 1) / 2 = (3 : ZMod 5)
      exact ((eq_div_iff_mul_eq (by decide : (2 : ZMod 5) ≠ 0)).2 (by decide)).symm
    · rintro ⟨i, hi⟩ - hne
      exfalso
      apply hne
      apply Subtype.ext
      fin_cases i
      · rfl
      · exact (hi rfl).elim
    · simp

end MathlibExtTest.Probability.Distributions.UniformDotProduct
