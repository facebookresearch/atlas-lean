/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalTensorFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketReturnExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhRepresentative

/-! Exact original seventh-axis local stabilizer and orbit,
from complete source-coordinate returns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual corrected Xi fixes the entire genuine canonical seventh axis. -/
theorem generatedSeventhXiPlaneCanonical_fixed :
    rhoLocal (localFiberIntoH generatedSeventhXiPlaneFiber)
      generatedSeventhXiPlaneCanonicalAxis = generatedSeventhXiPlaneCanonicalAxis :=
  generatedSeventhXiPlaneCanonical_fixed_of_returns generatedSeventhXiPlaneCanonicalShort_fixed
    generatedSeventhXiPlaneCanonicalTensor_fixed

/-- The actual full-axis stabilizer contains the original corrected moving-Xi projection. -/
theorem generatedSeventhXiPlane_projected :
    QuotientGroup.mk' signsSubgroup generatedSeventhXiPlaneFiber.val.2 ∈
      generatedSeventhProjectedAxisStabilizer :=
  generatedSeventhXiPlane_projected_of_returns generatedSeventhXiPlaneCanonicalShort_fixed
    generatedSeventhXiPlaneCanonicalTensor_fixed

/-- Every actual matrix-preserving Conway projection has a genuine full-axis fixing lift. -/
theorem generatedSeventh_projected_stabilizer_eq :
    generatedSeventhProjectedAxisStabilizer = generatedSeventhCo1SpatialStabilizer :=
  generatedSeventh_projection_eq_spatial_of_xi generatedSeventhXiPlane_projected

/-- The complete original seventh-axis stabilizer has exactly 318504960 elements. -/
theorem generatedSeventh_local_stabilizer_card :
    Nat.card generatedSeventhLocalAxisStabilizer = 318504960 :=
  generatedSeventh_local_stabilizer_card_of_xi generatedSeventhXiPlane_projected

/-- The actual seventh local-axis stabilizer has the genuine index 438020931059712000 in H. -/
theorem generatedSeventhLocalAxisStabilizer_index :
    generatedSeventhLocalAxisStabilizer.index = 438020931059712000 := by
  have h := generatedSeventhLocalAxisStabilizer.card_mul_index
  rw [generatedSeventh_local_stabilizer_card, local_h_card_exact] at h
  omega

/-- The original local orbit of the literal seventh representative. -/
def generatedSeventhLocalAxisOrbit : Set GriessSpace := MulAction.orbit H generatedSeventhAxis

/-- Exactly 438020931059712000 genuine vectors occur in this actual local axis orbit. -/
theorem generatedSeventhLocalAxisOrbit_card :
    Nat.card generatedSeventhLocalAxisOrbit = 438020931059712000 := by
  have h := generatedSeventhLocalAxisStabilizer_index
  rw [generatedSeventhLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- Every counted local-axis vector belongs to the genuine global axis orbit. -/
theorem generatedSeventhLocalAxisOrbit_subset_generated (r : GriessShortIndex) (c : ZMod 2) :
    generatedSeventhLocalAxisOrbit ⊆ generatedVectorOrbit (conwayShortAxis r c) := by
  rintro x ⟨h, hh⟩
  obtain ⟨g, hg⟩ := generatedSeventhAxis_mem_generatedOrbit r c
  refine ⟨localIntoGenerated h * g, ?_⟩
  change rhoLocal h (g.val (conwayShortAxis r c)) = x
  rw [hg]
  exact hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
