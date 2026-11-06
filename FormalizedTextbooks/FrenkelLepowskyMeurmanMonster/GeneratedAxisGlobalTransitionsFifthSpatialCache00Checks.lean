/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthSpatialCache00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthSpatialEntries

/-! Complete finite original-source checks for the root-zero rational spatial cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 50000000 in
-- Check every original Xi, coordinate sign, and phased source permutation spatial entry.
set_option maxRecDepth 10000 in
/-- All seven full stage matrices have their genuine original source entries. -/
theorem generatedAxisGlobalFifthSpatialCache00_stage_entries (h : Fin 7) (i j : Fin 24) :
    (if generatedAxisGlobalFifthShortNormalizationXi 0 h then
      co1XiMatrixQ i ((generatedAxisGlobalFifthShortNormalizationPermutation 0 h).val j)
    else if i = (generatedAxisGlobalFifthShortNormalizationPermutation 0 h).val j then
      1 else 0) *
    (if (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns 0 h)).val
      ((generatedAxisGlobalFifthShortNormalizationPermutation 0 h).val j) = 0 then 1 else -1) =
        generatedAxisGlobalFifthSpatialCache00Stage h i j := by
  revert h i j
  decide +kernel

/-- The entire cached stage operator is exactly the actual original rational source matrix. -/
theorem generatedAxisGlobalFifthSpatialCache00_stage_actual (h : Fin 7) :
    generatedAxisGlobalFifthSpatialStageMatrix 0 h =
      generatedAxisGlobalFifthSpatialCache00Stage h := by
  ext i j
  rw [generatedAxisGlobalFifthSpatialStageMatrix_entry]
  exact generatedAxisGlobalFifthSpatialCache00_stage_entries h i j

set_option maxHeartbeats 50000000 in
-- Check all seven complete576-entry rational matrix multiplication identities.
set_option maxRecDepth 10000 in
/-- Each full cached source stage carries its entire previous matrix to the next one. -/
theorem generatedAxisGlobalFifthSpatialCache00_steps (h : Fin 7) :
    generatedAxisGlobalFifthSpatialCache00Stage h *
      generatedAxisGlobalFifthSpatialCache00State h.castSucc =
        generatedAxisGlobalFifthSpatialCache00State h.succ := by
  revert h
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Check every entry of the complete initial identity matrix.
/-- The actual chronological matrix chain begins at the identity. -/
theorem generatedAxisGlobalFifthSpatialCache00_initial :
    generatedAxisGlobalFifthSpatialCache00State 0 = 1 := by
  decide +kernel

set_option maxHeartbeats 50000000 in
-- Check every normalized physical matrix coordinate from its complete rational source word.
set_option maxRecDepth 10000 in
/-- The cached source matrix determines all576 original normalized matrix coordinates. -/
theorem generatedAxisGlobalFifthSpatialCache00_matrix_checked (i j : Fin 24) :
    (∑ t : Fin 24, generatedAxisGlobalFifthSpatialCache00State 7 i t *
      (if Nat.testBit 0x0f000f t.val then (1 / 2 : ℚ) else 1 / 4) *
        generatedAxisGlobalFifthSpatialCache00State 7 j t) =
          generatedAxisGlobalFifthSpatialCache00Matrix i j := by
  revert i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
