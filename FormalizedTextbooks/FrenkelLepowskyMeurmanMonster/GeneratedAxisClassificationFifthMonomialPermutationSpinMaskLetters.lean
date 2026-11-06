/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinMaskPlan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanData

/-! Complete original signed source-letter rows bound to the existing certified spin models. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original source-letter rows, retaining the full unnormalized Parker coefficient matrices. -/
def generatedFifthSpinMaskLetterRows (l : Fin 2 × Bool) : generatedFifthSpinMaskRows :=
  if l.2 then
    ⟨fun i => (representativeNodeCoordinateRows (Fin.castAdd 13 l.1) i).val,
      fun i => (representativeNodePhaseRows (Fin.castAdd 13 l.1) i).val⟩
  else
    ⟨fun i => (representativeNodeInverseRows (Fin.castAdd 13 l.1) i).val,
      fun i => (representativeNodeInversePhaseRows (Fin.castAdd 13 l.1) i).val⟩

/-- Decoding the literal masks gives the genuine full signed source-letter model. -/
theorem generatedFifth_spin_mask_letter_model (l : Fin 2 × Bool) :
    generatedFifthSpinMaskRowsModel (generatedFifthSpinMaskLetterRows l) =
      generatedFourthMonomialLetterModel l := by
  rcases l with ⟨i, b⟩
  cases b <;> rfl

/-- Exact twelve-dimensional identity rows. -/
def generatedFifthSpinMaskIdentity : generatedFifthSpinMaskRows :=
  ⟨![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048], fun _ => 0⟩

/-- The row mask identity denotes the genuine identity spin model. -/
theorem generatedFifth_spin_mask_identity :
    generatedFifthSpinMaskRowsModel generatedFifthSpinMaskIdentity =
      representativeSpinIdentityModel := by
  have h : ∀ i j : Fin 12,
      (generatedFifthSpinMaskRowsModel generatedFifthSpinMaskIdentity).coordinate i j =
        representativeSpinIdentityModel.coordinate i j := by decide +kernel
  have hP := funext (fun i => funext (h i))
  change monsterCo1GeometryBinaryMaskMatrix generatedFifthSpinMaskIdentity.coordinate = 1 at hP
  change RepresentativeSpinModel.mk _ _ = RepresentativeSpinModel.mk _ _
  have hM : monsterCo1GeometryBinaryMaskMatrix generatedFifthSpinMaskIdentity.phase = 0 := by
    funext i j
    simp [monsterCo1GeometryBinaryMaskMatrix, monsterCo1GeometryBinaryMaskDecode,
      generatedFifthSpinMaskIdentity]
  rw [hP, hM]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
