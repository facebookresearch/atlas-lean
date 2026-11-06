/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2CoordinateTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2FlagAction

/-! Exact actual A2-plane flag stabilizers are transported with both geometric objects. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The counted actual selected-section flag subgroup is its genuine two-object stabilizer. -/
theorem leechSeventhE8A2FlagStabilizer_eq_action (W : leechSeventhE8A2Planes) :
    leechSeventhE8A2FlagStabilizer W = MulAction.stabilizer leechIsomSubgroup
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad), W.val) := by
  ext e
  rw [leechSeventhE8A2FlagStabilizer_mem]
  change _ ↔ e • (generatedAxisE8CoordinateSection
    (golayOctadWord generatedFifthFlagOctad), W.val) =
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad), W.val)
  rw [Prod.ext_iff]
  rfl

/-- Every genuine image-section and incident intrinsic A2 plane has stabilizer order 159252480. -/
theorem leechSeventhA2Flag_image_stabilizer_card (g : leechIsomSubgroup)
    (W : Submodule ℝ (Fin 24 → ℝ))
    (hW : W ∈ leechSeventhA2PlanesIn
      (generatedAxisE8ImageSection g (golayOctadWord generatedFifthFlagOctad))) :
    Nat.card (MulAction.stabilizer leechIsomSubgroup
      (generatedAxisE8ImageSection g (golayOctadWord generatedFifthFlagOctad), W)) =
        159252480 := by
  let S := generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)
  let V := (leechSeventhA2PlanesInEquiv g S).symm ⟨W, hW⟩
  have hV : V.val ∈ leechSeventhE8A2Planes := by
    rw [leechSeventhE8A2Planes_eq_intrinsic]
    exact V.property
  let P : leechSeventhE8A2Planes := ⟨V.val, hV⟩
  have he : (generatedAxisE8ImageSection g (golayOctadWord generatedFifthFlagOctad), W) =
      g • (S, P.val) := by
    apply Prod.ext
    · rfl
    · exact (congrArg Subtype.val
        ((leechSeventhA2PlanesInEquiv g S).apply_symm_apply ⟨W, hW⟩)).symm
  rw [← Nat.card_congr (MulAction.stabilizerEquivStabilizer he).toEquiv,
    ← leechSeventhE8A2FlagStabilizer_eq_action, leechSeventhE8A2FlagStabilizer_card]

/-- Every coordinate section and incident intrinsic A2 plane has actual Co0 stabilizer 159252480. -/
theorem leechSeventhA2Flag_coordinate_stabilizer_card (o : Fin 759)
    (W : Submodule ℝ (Fin 24 → ℝ))
    (hW : W ∈ leechSeventhA2PlanesIn
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Nat.card (MulAction.stabilizer leechIsomSubgroup
      (generatedAxisE8CoordinateSection (golayOctadWord o), W)) = 159252480 := by
  obtain ⟨g, hg⟩ := leechSeventh_coordinate_section_reachable o
  rw [← hg] at hW ⊢
  exact leechSeventhA2Flag_image_stabilizer_card g W hW

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
