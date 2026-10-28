/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMonomialGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignLift

/-! Actual sign membership and the remaining five full-axis generator obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The first ten orbit generators are the exact original equal-sign code generators. -/
theorem sixthFrameOrbitOriginalGenerator_sign (j : Fin 10) :
    sixthFrameOrbitOriginalGenerator (Fin.castAdd 5 j) =
      (QuotientGroup.mk (golaySignIsometry
        (sourceGeneratedSignCode (generatedSixthMonomialSignCode j))) : Co1) := by
  unfold sixthFrameOrbitOriginalGenerator sixthFrameOrbitOriginalIsometry
  have h : (Fin.castAdd 5 j).val < 14 := by
    change j.val < 14
    omega
  rw [dite_eq_left h]
  change QuotientGroup.mk' signsSubgroup (sixthFrameOrbitMonomialIsometry
    ⟨j.val, by omega⟩) = _
  unfold sixthFrameOrbitMonomialIsometry
  rw [dite_eq_left j.isLt, sixthFrameOrbit_sign_labels]
  rfl

/-- The last five orbit generators retain exactly the original raw fiber projections. -/
theorem sixthFrameOrbitOriginalGenerator_raw (j : Fin 5) :
    sixthFrameOrbitOriginalGenerator (Fin.natAdd 10 j) =
      (QuotientGroup.mk' signsSubgroup (generatedSixthRawGenerator j).val.2 : Co1) := by
  fin_cases j <;> rfl

/-- All ten original signs have genuine full-axis lifts in the projected stabilizer. -/
theorem sixthFrameOrbit_sign_mem (j : Fin 10) :
    sixthFrameOrbitOriginalGenerator (Fin.castAdd 5 j) ∈
      generatedSixthProjectedAxisStabilizer := by
  rw [sixthFrameOrbitOriginalGenerator_sign]
  exact generatedSixth_monomial_sign_projected_mem j

/-- The five corrected full-axis memberships suffice for the complete actual generator family. -/
theorem sixthFrameOrbit_generators_mem_of_corrected
    (h : ∀ j : Fin 5, projH (localFiberIntoH (generatedSixthCorrectedGenerator j)) ∈
      generatedSixthProjectedAxisStabilizer) (k : Fin 15) :
    sixthFrameOrbitOriginalGenerator k ∈ generatedSixthProjectedAxisStabilizer := by
  by_cases hk : k.val < 10
  · have he : k = Fin.castAdd 5 (⟨k.val, hk⟩ : Fin 10) := Fin.ext rfl
    rw [he]
    exact sixthFrameOrbit_sign_mem _
  · let j : Fin 5 := ⟨k.val - 10, by omega⟩
    have he : k = Fin.natAdd 10 j := by apply Fin.ext; dsimp [j]; omega
    rw [he, sixthFrameOrbitOriginalGenerator_raw,
      ← generatedSixth_corrected_generator_projection]
    exact h j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
