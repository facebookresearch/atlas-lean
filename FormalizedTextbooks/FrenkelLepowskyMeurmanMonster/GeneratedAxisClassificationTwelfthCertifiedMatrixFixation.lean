/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedKernelMatrixFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateMatrixSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactRootProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! Every genuine candidate fixes the entire actual matrix through original source Conway classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- All twelve complete constructed candidates retain genuine original whole-matrix fixation. -/
theorem generatedTwelfth_certified_original_matrix_fix (g : Fin 12) :
    generatedTwelfthCertifiedSpatial g ∈ generatedTwelfthSpatialStabilizer := by
  by_cases hg : g.val < 3
  · let k : Fin 3 := ⟨g.val, hg⟩
    have hk : (⟨k.val, by omega⟩ : Fin 12) = g := by rfl
    have hproj := generatedTwelfth_certified_spatial_source_projection g
    have he := generatedAxisGlobalMatrixAction_eq_of_projection
      (generatedTwelfthCertifiedSpatial g) (generatedTwelfthSpinCompactSpatial g) hproj
    change conwayMatrixAction (generatedTwelfthCertifiedSpatial g)
      (griessConwayEncode generatedTwelfthAxis).1 = (griessConwayEncode generatedTwelfthAxis).1
    rw [he]
    simpa only [hk] using generatedTwelfth_spin_compact_root_matrix_fixing k
  · let k : Fin 9 := ⟨g.val - 3, by omega⟩
    have hk : generatedTwelfthCertifiedKernelIndex k = g := by
      apply Fin.ext
      simp only [generatedTwelfthCertifiedKernelIndex, k]
      omega
    have h := generatedTwelfth_certified_kernel_letter_matrix_mem k
    change generatedTwelfthCertifiedSpatial (generatedTwelfthCertifiedKernelIndex k) ∈
      generatedTwelfthSpatialStabilizer at h
    simpa only [hk] using h

/-- Every genuine constructed local lift preserves the complete matrix of the actual candidate axis. -/
theorem generatedTwelfth_certified_candidate_matrix_fix (g : Fin 12) :
    (griessConwayEncode (rhoLocal (generatedTwelfthCertifiedLocal g)
      generatedTwelfthIncomingCandidateAxis)).1 =
      (griessConwayEncode generatedTwelfthIncomingCandidateAxis).1 := by
  rw [generatedTwelfthCertifiedLocal, generatedFourth_local_matrix]
  change conwayMatrixAction (generatedTwelfthCertifiedSpatial g)
    (griessConwayEncode generatedTwelfthIncomingCandidateAxis).1 =
      (griessConwayEncode generatedTwelfthIncomingCandidateAxis).1
  rw [generatedTwelfth_candidate_original_matrix]
  exact generatedTwelfth_certified_original_matrix_fix g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
