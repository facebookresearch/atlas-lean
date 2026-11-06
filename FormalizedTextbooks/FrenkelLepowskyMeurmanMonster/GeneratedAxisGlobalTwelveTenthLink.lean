/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthDecompose
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs

/-! Turning known triality images at any Tenth coset into bindings of a Tenth root word.

If both triality images at a local element `h` lie in the twelve-family union, and a word in the
six gated Tenth letters carries the binary root of root word `k` to the binary root of `h`, then
both images at root word `k` lie in the union (under the two pending fixers, the word is the
projection of a whole-axis stabilizer element). A whole transport of another family into the
Tenth orbit supplies such an `h`: one image is the source vector and the other is the source
family's opposite triality image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem sExtra_inv_eq_square_link (y : GriessSpace) :
    sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- Known triality images at a Tenth coset bind the root word whose binary root a gated letter
word carries to the binary root of that coset. -/
theorem generatedAxisGlobalTwelveTenth_root_pair_of_word
    (hfix : GeneratedAxisGlobalTwelveTenthFixers) (k : Fin 65) (h : H) (w : List (Fin 6))
    (hw : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedTenthAxisLowerRecoveryThreeProjectionMaskWord w
        (generatedAxisGlobalTwelveTenthRootMask k)) = (generatedAxisGlobalBinaryRoot h).val)
    (hpos : sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative 11)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative 11)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hword : generatedTenthAxisLowerRecoveryThreeProjectionWord w ∈
      (MulAction.stabilizer H generatedTenthAxis).map projH := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact generatedAxisGlobalTwelveTenth_letter_mem hfix g
  obtain ⟨c, hc, hcp⟩ := hword
  apply generatedAxisGlobalTwelve_root_pair_mem _ (generatedAxisGlobalTwelveRepresentative 11)
    h (generatedAxisGlobalTwelveTenthRootWord k) c hc _ hpos hneg
  apply Subtype.ext
  change co1BinaryAction (projH c)
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTenthRootWord k)).val = _
  rw [generatedAxisGlobalTwelveTenthRootWord_root, hcp,
    generatedTenth_axis_lower_recovery_three_projection_word_action
      generatedTenth_compact_spatial_binary_all, hw]

/-- A forward whole transport of a listed family into the Tenth orbit gives both triality images
at the target coset: the inverse image is the source vector, and the forward image is the
source family's inverse triality image. -/
theorem generatedAxisGlobalTwelveTenth_pair_of_forward_transport (j : Fin 12) (x : H) (h : H)
    (htrans : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal h (generatedAxisGlobalTwelveRepresentative 11))
    (hsrc : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← htrans]
  refine ⟨?_, ?_⟩
  · rw [← sExtra_inv_eq_square_link]
    exact hsrc
  · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport j x rfl

/-- An inverse whole transport of a listed family into the Tenth orbit gives both triality
images at the target coset: the forward image is the source vector, and the inverse image is
the source family's forward triality image. -/
theorem generatedAxisGlobalTwelveTenth_pair_of_inverse_transport (j : Fin 12) (x : H) (h : H)
    (htrans : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal h (generatedAxisGlobalTwelveRepresentative 11))
    (hsrc : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← htrans]
  refine ⟨?_, ?_⟩
  · rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport j x rfl
  · have e : sExtra⁻¹ (sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j))) =
        sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) := by
      rw [sExtra_inv_eq_square_link (sExtra⁻¹ _), LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply]
    rw [e]
    exact hsrc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
