/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact coordinate dictionaries on the actual matrix and short constituents. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerPlusCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual matrix constituent is linearly equivalent to the full symmetric matrix space. -/
noncomputable def generatedCentralMatrixCoordinates : generatedCentralMatrix ≃ₗ[ℝ] Sym24 where
  toFun x := (generatedCentralPlusCoordinates x.val).1
  invFun A := ⟨generatedCentralPlusEmbed A 0, by
    rw [mem_generatedCentralMatrix, generatedCentralPlusCoordinates_snd,
      generatedCentralPlusEmbed_encode]⟩
  left_inv x := by
    apply Subtype.ext
    apply generatedCentralPlusCoordinates.injective
    apply Prod.ext
    · apply Subtype.ext
      change (griessConwayEncode (generatedCentralPlusEmbed
        (generatedCentralPlusCoordinates x.val).1 0).val).1 = _
      rw [generatedCentralPlusEmbed_encode]
    · change (generatedCentralPlusCoordinates (generatedCentralPlusEmbed
        (generatedCentralPlusCoordinates x.val).1 0)).2 =
          (generatedCentralPlusCoordinates x.val).2
      rw [generatedCentralPlusCoordinates_snd, generatedCentralPlusEmbed_encode]
      exact ((mem_generatedCentralMatrix x.val).mp x.property).symm
  right_inv A := by
    apply Subtype.ext
    change (griessConwayEncode (generatedCentralPlusEmbed A 0).val).1 = A.val
    rw [generatedCentralPlusEmbed_encode]
  map_add' x y := congrArg Prod.fst (generatedCentralPlusCoordinates.map_add x.val y.val)
  map_smul' c x := congrArg Prod.fst (generatedCentralPlusCoordinates.map_smul c x.val)

/-- The actual short constituent is linearly equivalent to its original short-label coefficients. -/
noncomputable def generatedCentralShortCoordinates :
    generatedCentralShort ≃ₗ[ℝ] (GriessShortIndex → ℝ) where
  toFun x := (generatedCentralPlusCoordinates x.val).2
  invFun X := ⟨generatedCentralPlusEmbed 0 X, by
    rw [mem_generatedCentralShort]
    apply Subtype.ext
    change (griessConwayEncode (generatedCentralPlusEmbed 0 X).val).1 = (0 : Sym24).val
    rw [generatedCentralPlusEmbed_encode]⟩
  left_inv x := by
    apply Subtype.ext
    apply generatedCentralPlusCoordinates.injective
    apply Prod.ext
    · apply Subtype.ext
      change (griessConwayEncode (generatedCentralPlusEmbed
        0 (generatedCentralPlusCoordinates x.val).2).val).1 =
          (generatedCentralPlusCoordinates x.val).1.val
      rw [generatedCentralPlusEmbed_encode]
      exact congrArg Subtype.val ((mem_generatedCentralShort x.val).mp x.property).symm
    · change (griessConwayEncode (generatedCentralPlusEmbed
        0 (generatedCentralPlusCoordinates x.val).2).val).2.1 = _
      rw [generatedCentralPlusEmbed_encode]
  right_inv X := by
    change (griessConwayEncode (generatedCentralPlusEmbed 0 X).val).2.1 = X
    rw [generatedCentralPlusEmbed_encode]
  map_add' x y := congrArg Prod.snd (generatedCentralPlusCoordinates.map_add x.val y.val)
  map_smul' c x := congrArg Prod.snd (generatedCentralPlusCoordinates.map_smul c x.val)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
