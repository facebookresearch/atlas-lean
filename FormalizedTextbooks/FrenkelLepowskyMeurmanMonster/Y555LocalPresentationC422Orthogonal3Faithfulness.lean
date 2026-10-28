/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine full local source faithfulness from original-source replay and checked image
separation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Finite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ImageLower
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationImageCardinality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Matching actual source and image bounds give exact local orders and the full source kernel. -/
theorem y422Orthogonal3_exact_order_faithful :
    Nat.card Y422Presentation = 9904359628800 ∧
      Nat.card y422Orthogonal3ProjectiveImage = 9904359628800 ∧
      Function.Injective y422Orthogonal3ProjectiveHom := by
  let := y422Presentation_finite_card.1
  have hl : 9904359628800 ≤ Nat.card ((⊤ : Subgroup Y422Presentation).map
      y422Orthogonal3ProjectiveHom) := by
    simpa only [Subgroup.map_top, y422Orthogonal3ProjectiveImage] using
      y422Orthogonal3ProjectiveImage_card_ge
  have hu : Nat.card (⊤ : Subgroup Y422Presentation) ≤ 9904359628800 := by
    simpa only [Subgroup.card_top] using y422Presentation_finite_card.2
  obtain ⟨hs, ht, hi⟩ := y322FiniteSubgroup_image_exact_order y422Orthogonal3ProjectiveHom ⊤
    9904359628800 hl hu
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Subgroup.card_top] using hs
  · simpa only [Subgroup.map_top, y422Orthogonal3ProjectiveImage] using ht
  · intro x y hxy
    have h : (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup Y422Presentation)) =
        ⟨y, Subgroup.mem_top y⟩ := hi hxy
    exact congrArg Subtype.val h

/-- The original nine-generator local source has no kernel in its concrete projective action. -/
theorem y422Orthogonal3ProjectiveHom_injective :
    Function.Injective y422Orthogonal3ProjectiveHom :=
  y422Orthogonal3_exact_order_faithful.2.2

/-- Original C422/S/Q is isomorphic to its concrete, faithfully recognized projective image. -/
noncomputable def y422Orthogonal3SourceImageEquiv :
    Y422Presentation ≃* y422Orthogonal3ProjectiveImage :=
  MonoidHom.ofInjective y422Orthogonal3ProjectiveHom_injective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
