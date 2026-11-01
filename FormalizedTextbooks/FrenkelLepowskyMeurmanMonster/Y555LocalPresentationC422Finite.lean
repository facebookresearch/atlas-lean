/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual finite order bound from the original C422/S/Q coset replay.
The printed orthogonal-group identification is not assumed by this bound. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetTransitions

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original nine-generator C422/S/Q presentation is finite with its source upper bound. -/
theorem y422Presentation_finite_card :
    Finite Y422Presentation ∧ Nat.card Y422Presentation ≤ 9904359628800 := by
  have : Finite y422C322Subgroup := y422C322Subgroup_finite_card.1
  obtain ⟨hfin, hcard⟩ := y555Finite_card_of_cosetCover y422C322Subgroup
    y422CosetRepresentative y422CosetRepresentative_cover
  refine ⟨hfin, hcard.trans ?_⟩
  calc
    Nat.card y422C322Subgroup * 1080 ≤ 9170703360 * 1080 :=
      Nat.mul_le_mul_right _ y422C322Subgroup_finite_card.2
    _ = 9904359628800 := by decide

/-- Its actual independent-Y444 local image is finite with the same proved source upper bound. -/
theorem y422IntoY444_range_finite_card :
    Finite y422IntoY444.range ∧ Nat.card y422IntoY444.range ≤ 9904359628800 := by
  have : Finite Y422Presentation := y422Presentation_finite_card.1
  let f : Y422Presentation → y422IntoY444.range := fun x => ⟨y422IntoY444 x, ⟨x, rfl⟩⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, x, rfl⟩
    exact ⟨x, rfl⟩
  exact ⟨Finite.of_surjective f hsurj,
    (Nat.card_le_card_of_surjective f hsurj).trans y422Presentation_finite_card.2⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
