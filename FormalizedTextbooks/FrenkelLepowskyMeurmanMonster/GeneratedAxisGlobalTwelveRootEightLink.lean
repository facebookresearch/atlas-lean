/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightDecompose
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs

/-! Turning known triality images at any root-eight coset into bindings of a root-eight root
word.

If both triality images at a local element `h` lie in the twelve-family union, and a word in the
four root-eight letters carries the binary root of root word `k` to the binary root of `h`, then
both images at root word `k` lie in the union (the word is the projection of a whole-axis
stabilizer element). A whole transport of another family into the root-eight orbit supplies
such an `h`: one image is the source vector and the other is the source family's opposite
triality image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem sExtra_inv_eq_square_rootEight (y : GriessSpace) :
    sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- Known triality images at a root-eight coset bind the root word whose binary root a letter
word carries to the binary root of that coset. -/
theorem generatedAxisGlobalTwelveRootEight_root_pair_of_word (k : Fin 23) (h : H)
    (w : List (Fin 4))
    (hw : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (rootEightForestWordApply w (rootEightForestRootMask k)) =
        (generatedAxisGlobalBinaryRoot h).val)
    (hpos : sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative 9)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative 9)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hword : (w.map (fun g => QuotientGroup.mk' signsSubgroup
      (rootEightForestIsometry g))).prod ∈
      (MulAction.stabilizer H generatedFifthRootEightAxis).map projH := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact rootEightForest_letter_mem_map g
  obtain ⟨c, hc, hcp⟩ := hword
  apply generatedAxisGlobalTwelve_root_pair_mem _ (generatedAxisGlobalTwelveRepresentative 9)
    h (rootEightForestRootWord k) c hc _ hpos hneg
  apply Subtype.ext
  change co1BinaryAction (projH c)
    (generatedAxisGlobalBinaryRoot (rootEightForestRootWord k)).val = _
  rw [rootEightForestRootWord_root, hcp, ← rootEightForestWordApply_decode rootEightForest_lifts,
    hw]

/-- A forward whole transport of a listed family into the root-eight orbit gives both triality
images at the target coset: the inverse image is the source vector, and the forward image is the
source family's inverse triality image. -/
theorem generatedAxisGlobalTwelveRootEight_pair_of_forward_transport (j : Fin 12) (x : H)
    (h : H)
    (htrans : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal h (generatedAxisGlobalTwelveRepresentative 9))
    (hsrc : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← htrans]
  refine ⟨?_, ?_⟩
  · rw [← sExtra_inv_eq_square_rootEight]
    exact hsrc
  · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport j x rfl

/-- An inverse whole transport of a listed family into the root-eight orbit gives both triality
images at the target coset: the forward image is the source vector, and the inverse image is
the source family's forward triality image. -/
theorem generatedAxisGlobalTwelveRootEight_pair_of_inverse_transport (j : Fin 12) (x : H)
    (h : H)
    (htrans : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal h (generatedAxisGlobalTwelveRepresentative 9))
    (hsrc : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← htrans]
  refine ⟨?_, ?_⟩
  · rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport j x rfl
  · have e : sExtra⁻¹ (sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j))) =
        sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) := by
      rw [sExtra_inv_eq_square_rootEight (sExtra⁻¹ _), LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply]
    rw [e]
    exact hsrc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
