/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! The exact sixth local stabilizer and orbit from all five genuine whole-axis lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Each corrected original fiber supplies its actual projection to the full-axis stabilizer. -/
theorem generatedSixth_corrected_generator_projected_mem (k : Fin 5) :
    projH (localFiberIntoH (generatedSixthCorrectedGenerator k)) ∈
      generatedSixthProjectedAxisStabilizer := by
  refine ⟨⟨localFiberIntoH (generatedSixthCorrectedGenerator k),
    generatedSixth_corrected_generator_full_fixed k⟩, ?_⟩
  rfl

/-- The genuine whole-axis projection exhausts the independently counted spatial flag group. -/
theorem generatedSixthProjectedAxisStabilizer_eq_spatial :
    generatedSixthProjectedAxisStabilizer = generatedSixthCo1SpatialStabilizer :=
  sixthFrameOrbit_projection_eq_of_corrected generatedSixth_corrected_generator_projected_mem

/-- The entire actual sixth-axis stabilizer in H has exactly 73,574,645,760 elements. -/
theorem generatedSixth_local_stabilizer_card :
    Nat.card generatedSixthLocalAxisStabilizer = 73574645760 :=
  generatedSixthLocalAxisStabilizer_card_of_projection
    generatedSixthProjectedAxisStabilizer_eq_spatial

/-- The genuine sixth-axis orbit under H has exactly 1,896,194,506,752,000 elements. -/
theorem generatedSixth_local_axis_orbit_card :
    Nat.card (MulAction.orbit H generatedSixthAxis) = 1896194506752000 := by
  have h := generatedSixthLocalAxisStabilizer.card_mul_index
  rw [generatedSixth_local_stabilizer_card, local_h_card_exact] at h
  have hi : generatedSixthLocalAxisStabilizer.index = 1896194506752000 := by omega
  rw [generatedSixthLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
