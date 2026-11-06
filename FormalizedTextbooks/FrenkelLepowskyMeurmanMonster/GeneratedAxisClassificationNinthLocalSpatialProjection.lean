/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpatialStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLocalStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The actual full-axis projection is contained in the counted whole-matrix stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Project the actual full-axis local stabilizer to the genuine Conway quotient. -/
def generatedNinthLocalAxisProjection : generatedNinthLocalAxisStabilizer →* Co1 :=
  projH.comp generatedNinthLocalAxisStabilizer.subtype

/-- The actual projection image, with no onto premise. -/
def generatedNinthProjectedAxisStabilizer : Subgroup Co1 :=
  generatedNinthLocalAxisProjection.range

/-- Full actual axis fixation implies fixation of its actual matrix component. -/
theorem generatedNinth_local_fiber_spatial_mem (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis) :
    f.val.2 ∈ generatedNinthSpatialStabilizer := by
  have hm := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  rw [generatedFourth_local_matrix] at hm
  exact hm

/-- The genuine full-axis image lies in the counted whole-matrix stabilizer. -/
theorem generatedNinthProjectedAxisStabilizer_le_spatial :
    generatedNinthProjectedAxisStabilizer ≤ generatedNinthCo1SpatialStabilizer := by
  rintro c ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis := by
    rw [hf]
    exact h.property
  refine ⟨f.val.2, generatedNinth_local_fiber_spatial_mem f hfix, ?_⟩
  change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
  rw [← hf]
  rfl

/-- The actual full-axis projection has at most89181388800 elements. -/
theorem generatedNinthProjectedAxisStabilizer_card_le :
    Nat.card generatedNinthProjectedAxisStabilizer ≤ 89181388800 := by
  let : Finite generatedNinthCo1SpatialStabilizer := Nat.finite_of_card_ne_zero
    (by rw [generatedNinthCo1SpatialStabilizer_card]; decide)
  rw [← generatedNinthCo1SpatialStabilizer_card]
  exact Subgroup.card_le_of_le generatedNinthProjectedAxisStabilizer_le_spatial

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
