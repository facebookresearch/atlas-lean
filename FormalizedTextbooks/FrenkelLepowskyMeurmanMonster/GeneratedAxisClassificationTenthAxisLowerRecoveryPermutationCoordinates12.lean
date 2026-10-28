/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates12Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates12Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationCoordinates12Block02

/-! Complete full 24-coordinate checks for original traversal entries540 through584. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check every original word and all twenty-four coordinates in this bounded block.
/-- Every original word in this 45-entry block retains all 24 actual coordinates. -/
theorem generatedTenth_axis_lower_recovery_traversal_coordinates_12 :
    ∀ u : Fin 45,
      generatedTenthAxisLowerRecoveryEvaluateWord
        (generatedTenthAxisLowerRecoveryTraversalWord ⟨540 + u.val, by omega⟩) =
          generatedTenthAxisLowerRecoveryTraversalForward ⟨540 + u.val, by omega⟩ := by
  have hblocks : ∀ b : Fin 3, ∀ v : Fin 15,
      generatedTenthAxisLowerRecoveryEvaluateWord
        (generatedTenthAxisLowerRecoveryTraversalWord
          ⟨540 + 15 * b.val + v.val, by omega⟩) =
        generatedTenthAxisLowerRecoveryTraversalForward
          ⟨540 + 15 * b.val + v.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_12_block00
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_12_block01
    · exact generatedTenth_axis_lower_recovery_traversal_coordinates_12_block02
  intro u
  let b : Fin 3 := ⟨u.val / 15, by omega⟩
  let v : Fin 15 := ⟨u.val % 15, Nat.mod_lt _ (by decide)⟩
  have hr : (⟨540 + 15 * b.val + v.val, by omega⟩ : Fin 720) =
      ⟨540 + u.val, by omega⟩ := by
    apply Fin.ext
    dsimp only [b, v]
    omega
  have h := hblocks b v
  rwa [hr] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
