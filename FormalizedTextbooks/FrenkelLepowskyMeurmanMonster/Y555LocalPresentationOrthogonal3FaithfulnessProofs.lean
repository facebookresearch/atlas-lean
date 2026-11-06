/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual local source orders and faithfulness from matching checked bounds. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationImageCardinality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Hom
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexCorrectedOrder

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The proved actual source upper bound and a matching image lower bound force faithfulness. -/
theorem y322Orthogonal3_exact_order_faithful_of_lower
    (lower : 9170703360 ≤ Nat.card y322Orthogonal3Image) :
    Nat.card Y322Presentation = 9170703360 ∧
      Nat.card y322Orthogonal3Image = 9170703360 ∧
      Function.Injective y322Orthogonal3Hom := by
  let := y322Presentation_finite_card.1
  have hl : 9170703360 ≤ Nat.card ((⊤ : Subgroup Y322Presentation).map
      y322Orthogonal3Hom) := by
    simpa only [Subgroup.map_top, y322Orthogonal3Image] using lower
  have hu : Nat.card (⊤ : Subgroup Y322Presentation) ≤ 9170703360 := by
    simpa only [Subgroup.card_top] using y322Presentation_finite_card.2
  obtain ⟨hs, ht, hi⟩ := y322FiniteSubgroup_image_exact_order y322Orthogonal3Hom ⊤
    9170703360 hl hu
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Subgroup.card_top] using hs
  · simpa only [Subgroup.map_top, y322Orthogonal3Image] using ht
  · intro x y hxy
    have h : (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup Y322Presentation)) =
        ⟨y, Subgroup.mem_top y⟩ := hi hxy
    exact congrArg Subtype.val h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
