/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatialCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhProjection

/-! Unconditional local seventh-axis bounds, with projected surjectivity still open. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Full seventh-axis fixation has at most 79626240 actual Conway projection values. -/
theorem generatedSeventhProjectedAxisStabilizer_card_le :
    Nat.card generatedSeventhProjectedAxisStabilizer ≤ 79626240 := by
  let : Finite Co1 := co1_finite
  let f : generatedSeventhProjectedAxisStabilizer → generatedSeventhCo1SpatialStabilizer :=
    fun g => ⟨g.val, generatedSeventhProjectedAxisStabilizer_le_spatial g.property⟩
  have hf : Function.Injective f := by
    intro g h he
    exact Subtype.ext (congrArg (fun x : generatedSeventhCo1SpatialStabilizer => x.val) he)
  simpa only [generatedSeventhCo1SpatialStabilizer_card] using Nat.card_le_card_of_injective f hf

/-- The full actual H stabilizer of the seventh representative has at most 318504960 elements. -/
theorem generatedSeventhLocalAxisStabilizer_card_le :
    Nat.card generatedSeventhLocalAxisStabilizer ≤ 318504960 := by
  rw [generatedSeventh_local_stabilizer_card_range]
  exact Nat.mul_le_mul_left 4 generatedSeventhProjectedAxisStabilizer_card_le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
