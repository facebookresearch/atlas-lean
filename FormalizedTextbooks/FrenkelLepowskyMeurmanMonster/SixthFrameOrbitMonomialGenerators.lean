/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthMonomialGeneration

/-! Exact original fourteen-generator comparison with the counted monomial subgroup. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The two internal catalogues use identical actual source sign labels. -/
theorem sixthFrameOrbit_sign_labels :
    sixthFrameOrbitSignLabels = generatedSixthMonomialSignCode := by
  decide +kernel

/-- Each original transported full fiber has the counted genuine permutation projection. -/
theorem sixthFrameOrbit_raw_spatial (j : Fin 3) :
    (generatedSixthRawGenerator (Fin.castAdd 2 j)).val.2 =
      golayPermutationIsometry (leechRootedA2SixthPermutationGenerator j) := by
  have hr : (generatedSixthRawGenerator (Fin.castAdd 2 j)).val.2 =
      generatedSixthPermutationTransportFiber.val.2 *
        (representativePermutationFiber (leechRootedA2ThreePointRepresentative j)).val.2 *
        generatedSixthPermutationTransportFiber.val.2⁻¹ := by
    fin_cases j <;> rfl
  rw [hr, leechRootedA2ThreePoint_fiber_spatial]
  have hb : generatedSixthPermutationTransportFiber.val.2 =
      golayPermutationIsometry leechRootedA2SixthPermutationTransport :=
    leechRootedA2GeneratingWordFiber_spatial _
  rw [hb]
  exact ((golayPermutationHom.map_mul _ _).trans
    (congrArg₂ (· * ·) (golayPermutationHom.map_mul _ _) (golayPermutationHom.map_inv _))).symm

/-- The original full swap fiber has exactly the counted genuine swap projection. -/
theorem sixthFrameOrbit_swap_spatial :
    (generatedSixthRawGenerator 3).val.2 =
      golayPermutationIsometry leechRootedA2SixthPermutationWordSwap :=
  leechRootedA2GeneratingWordFiber_spatial _

/-- All fourteen original monomial matrices fix the genuine starting frame vector. -/
theorem sixthFrameOrbit_monomial_frame_check : ∀ k : Fin 14,
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns (Fin.castAdd 1 k)) 2048 = 2048 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
