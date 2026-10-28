/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeProjectionGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedKernelActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthProjectionCountGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactRootProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthLocalUpper

/-! Only three complete genuine candidate fixers are needed for the actual local count.
The whole original root and kernel values are attained through checked Conway word relations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Whole actual-axis fixation for the three genuine compatible candidate lifts. -/
def generatedTwelfthThreeCandidateAxisFixation : Prop :=
  ∀ g : Fin 3,
    rhoLocal (generatedTwelfthCertifiedLocal ⟨g.val, by omega⟩)
      generatedTwelfthIncomingCandidateAxis = generatedTwelfthIncomingCandidateAxis

/-- Every one of the three genuinely fixed candidate Conway values is actually attained. -/
theorem generatedTwelfth_three_actual_projection_mem
    (hfix : generatedTwelfthThreeCandidateAxisFixation) (g : Fin 3) :
    generatedTwelfthThreeProjectionLetter g ∈ generatedTwelfthProjectedAxisStabilizer := by
  obtain ⟨k, hk, haxis⟩ := generatedTwelfth_incoming_candidate_fixer_transfer
    (generatedTwelfthCertifiedLocal ⟨g.val, by omega⟩) (hfix g)
  change projH k = generatedTwelfthThreeProjectionLetter g at hk
  exact ⟨⟨k, haxis⟩, hk⟩

/-- The actual stabilizer attains all twelve known candidate Conway values through three fixers. -/
theorem generatedTwelfth_three_all_candidate_projection_mem
    (hfix : generatedTwelfthThreeCandidateAxisFixation) (g : Fin 12) :
    (QuotientGroup.mk (generatedTwelfthCertifiedSpatial g) : Co1) ∈
      generatedTwelfthProjectedAxisStabilizer :=
  generatedTwelfth_three_projection_candidates_mem generatedTwelfthProjectedAxisStabilizer
    (generatedTwelfth_three_actual_projection_mem hfix) g

/-- The unchanged original root-generator Conway values are attained by the actual fixers. -/
theorem generatedTwelfth_three_root_projection_mem
    (hfix : generatedTwelfthThreeCandidateAxisFixation) (g : Fin 3) :
    (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) ∈
      generatedTwelfthProjectedAxisStabilizer := by
  have he : (QuotientGroup.mk (generatedTwelfthCertifiedSpatial ⟨g.val, by omega⟩) : Co1) =
      QuotientGroup.mk (generatedTwelfthMatrixFixer g).val :=
    (generatedTwelfth_certified_spatial_source_projection ⟨g.val, by omega⟩).trans
      (generatedTwelfth_spin_compact_root_spatial_projection g)
  rw [← he]
  exact generatedTwelfth_three_all_candidate_projection_mem hfix _

/-- Three complete actual fixers suffice for the entire actual projected count 3,686,400. -/
theorem generatedTwelfth_three_actual_projected_axis_stabilizer_card
    (hfix : generatedTwelfthThreeCandidateAxisFixation) :
    Nat.card generatedTwelfthProjectedAxisStabilizer = 3686400 := by
  apply Nat.le_antisymm
  · exact generatedTwelfth_projected_card_le_spatial.trans
      generatedTwelfth_Co1_spatial_stabilizer_upper
  · exact generatedTwelfth_projection_card_lower_generic generatedTwelfthProjectedAxisStabilizer
      (generatedTwelfth_three_root_projection_mem hfix)
      (generatedTwelfth_certified_kernel_projection_mem generatedTwelfthProjectedAxisStabilizer
        (generatedTwelfth_three_all_candidate_projection_mem hfix))

/-- Three complete actual fixers suffice for the entire actual local count 3,686,400. -/
theorem generatedTwelfth_three_actual_local_axis_stabilizer_card
    (hfix : generatedTwelfthThreeCandidateAxisFixation) :
    Nat.card generatedTwelfthLocalAxisStabilizer = 3686400 := by
  rw [generatedTwelfth_local_stabilizer_card_range,
    generatedTwelfth_three_actual_projected_axis_stabilizer_card hfix]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
