/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Intrinsic

/-! Genuine lattice isometries transport intrinsic A2 planes between actual sections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Preferred physical short images retain precisely the actual integral orientation. -/
theorem leechSeventh_short_real_image_sign (g : leechIsomSubgroup) (r : GriessShortIndex) :
    g.val (griessShortVector r) = griessShortVector (griessShortPermutation g r) ∨
      g.val (griessShortVector r) = -griessShortVector (griessShortPermutation g r) := by
  have he : g.val (griessShortVector r) =
      leechCoordinateEmbedding (leechIntegralAction g (griessShortLatticeVector r)).val :=
    (leechIntegralAction_embedding g (griessShortLatticeVector r)).symm
  rw [he]
  rcases generatedE8Short_integral_sign g r with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h, Submodule.coe_neg, map_neg]
    rfl

/-- Every actual isometry preserves absolute preferred physical short pairing. -/
theorem leechSeventh_short_pairing_abs_image (g : leechIsomSubgroup)
    (r s : GriessShortIndex) :
    |stdPairingFun (griessShortVector (griessShortPermutation g r))
      (griessShortVector (griessShortPermutation g s))| =
        |stdPairingFun (griessShortVector r) (griessShortVector s)| := by
  have h := leechSeventh_pairing_abs_sign _ _ _ _
    (leechSeventh_short_real_image_sign g r) (leechSeventh_short_real_image_sign g s)
  rw [g.property.1] at h
  exact h.symm

/-- The real image of an intrinsic A2 plane is intrinsic in the actual image integral section. -/
theorem leechSeventhA2PlanesIn_map_mem (g : leechIsomSubgroup)
    (S : Submodule ℤ leechIntegral) (W : Submodule ℝ (Fin 24 → ℝ))
    (hW : W ∈ leechSeventhA2PlanesIn S) :
    W.map g.val.toLinearMap ∈
      leechSeventhA2PlanesIn (S.map (leechIntegralAction g).toLinearMap) := by
  rcases hW with ⟨r, s, hr, hs, hrs, rfl⟩
  refine ⟨griessShortPermutation g r, griessShortPermutation g s,
    (generatedAxisE8ShortLines_image_mem g S r).mpr hr,
    (generatedAxisE8ShortLines_image_mem g S s).mpr hs, ?_, ?_⟩
  · rw [leechSeventh_short_pairing_abs_image, hrs]
  · rw [Submodule.map_span, Set.image_pair]
    change Submodule.span ℝ {g.val (griessShortVector r), g.val (griessShortVector s)} = _
    exact leechSeventh_span_pair_sign _ _ _ _
      (leechSeventh_short_real_image_sign g r) (leechSeventh_short_real_image_sign g s)

/-- Actual section transport gives an equivalence of the complete intrinsic A2-plane carriers. -/
def leechSeventhA2PlanesInEquiv (g : leechIsomSubgroup) (S : Submodule ℤ leechIntegral) :
    leechSeventhA2PlanesIn S ≃
      leechSeventhA2PlanesIn (S.map (leechIntegralAction g).toLinearMap) where
  toFun W := ⟨W.val.map g.val.toLinearMap, leechSeventhA2PlanesIn_map_mem g S W.val W.property⟩
  invFun W := ⟨W.val.map g.val.symm.toLinearMap, by
    have h := leechSeventhA2PlanesIn_map_mem g⁻¹
      (S.map (leechIntegralAction g).toLinearMap) W.val W.property
    have hS : (S.map (leechIntegralAction g).toLinearMap).map
        (leechIntegralAction g⁻¹).toLinearMap = S := by
      rw [map_inv]
      change (S.map (leechIntegralAction g).toLinearMap).map
        (leechIntegralAction g).symm.toLinearMap = S
      rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
    rwa [hS] at h⟩
  left_inv W := by
    apply Subtype.ext
    change (W.val.map g.val.toLinearMap).map g.val.symm.toLinearMap = W.val
    rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
  right_inv W := by
    apply Subtype.ext
    change (W.val.map g.val.symm.toLinearMap).map g.val.toLinearMap = W.val
    rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]

/-- Every genuine image of the selected section has exactly 1120 intrinsic actual A2 planes. -/
theorem leechSeventhA2PlanesIn_image_card (g : leechIsomSubgroup) :
    Nat.card (leechSeventhA2PlanesIn
      (generatedAxisE8ImageSection g (golayOctadWord generatedFifthFlagOctad))) = 1120 := by
  change Nat.card (leechSeventhA2PlanesIn
    ((generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)).map
      (leechIntegralAction g).toLinearMap)) = _
  rw [← Nat.card_congr (leechSeventhA2PlanesInEquiv g _),
    ← leechSeventhE8A2Planes_eq_intrinsic, leechSeventhE8A2Planes_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
