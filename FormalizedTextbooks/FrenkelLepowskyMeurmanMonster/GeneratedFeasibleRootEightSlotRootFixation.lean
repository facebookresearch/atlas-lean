/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleRootEightSlotFeasibility
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFlagRecognition
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFinalPairQ
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightSpatialProjection

/-! Every actual whole-axis fixer of the counted root-eight prototype fixes its rooted pair axis.

The rooted label is the plus pair on coordinates sixteen and seventeen, whose integral vector is
the distinguished norm 4 vector of the root-eight matrix flag. The spatial part of every fixer
preserves that lattice line, hence fixes the label, and the nonzero final short coefficient
3/16 on that label forces the central phase to vanish. This is the size-one first-axis
catalogue of source slot 9 (label 10A1) of Höhn–Seysen, arXiv:2508.01037, Table 3. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The rooted plus pair label has exactly the distinguished norm 4 integral coordinates. -/
theorem generatedFeasibleRootEightSlot_root_integral :
    griessShortIntegral (Sum.inl (1, 248)) = generatedFifthRootEightNormFourVector := by
  funext i
  simp only [griessShortIntegral, generatedFeasibleRootEightSlot_root_coordinates]
  revert i
  decide +kernel

/-- The rooted short vector is the real embedding of the distinguished norm 4 lattice vector. -/
theorem generatedFeasibleRootEightSlot_root_short_vector :
    griessShortVector (Sum.inl (1, 248)) =
      leechCoordinateEmbedding generatedFifthRootEightNormFour.val := by
  funext i
  change (griessShortIntegral (Sum.inl (1, 248)) i : ℝ) / Real.sqrt 8 =
    (generatedFifthRootEightNormFourVector i : ℝ) / Real.sqrt 8
  rw [generatedFeasibleRootEightSlot_root_integral]

/-- The spatial part of every actual whole-axis fixer fixes the rooted plus pair label. -/
theorem generatedFeasibleRootEightSlot_spatial_root (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedFifthRootEightAxis =
      generatedFifthRootEightAxis) :
    griessShortPermutation f.val.2 (Sum.inl (1, 248)) = Sum.inl (1, 248) := by
  have hm := generatedFifthRootEight_local_fiber_spatial_mem f hf
  have hl := ((generatedFifthRootEight_matrix_fix_integral_lines_iff f.val.2).mp hm).2
  apply monsterNortonShortPermutation_of_vector
  rw [generatedFeasibleRootEightSlot_root_short_vector, ← leechIntegralAction_embedding]
  rcases hl with h | h
  · left
    rw [h]
  · right
    rw [h]
    exact map_neg leechCoordinateEmbedding generatedFifthRootEightNormFour.val

/-- The exact rational final short coefficient on the rooted label is 3/16. -/
theorem generatedFeasibleRootEightSlot_root_pair_q :
    generatedFifthRootEightFinalPairQ 1 248 = 3 / 16 := by
  have hm : generatedFifthRootEightIncomingMatrixQ 16 17 = -1 / 16 := by
    decide +kernel
  have h0 : generatedFifthRootEightIncomingPairNumerator 0 248 = 0 := by
    decide +kernel
  have h1 : generatedFifthRootEightIncomingPairNumerator 1 248 = -4 := by
    decide +kernel
  unfold generatedFifthRootEightFinalPairQ
  simp only [generatedFeasibleRootEightSlot_root_coordinates]
  rw [hm, h0, h1]
  norm_num

/-- The actual final root-eight short coefficient on the rooted label is 3/16. -/
theorem generatedFeasibleRootEightSlot_root_coefficient :
    (griessConwayEncode generatedFifthRootEightAxis).2.1 (Sum.inl (1, 248)) = 3 / 16 := by
  rw [generatedFifthRootEight_final_pair_q, generatedFeasibleRootEightSlot_root_pair_q]
  norm_num

/-- Every actual local fixer of the root-eight prototype fixes both signs of its rooted
plus pair axis over `(16, 17)`. -/
theorem generatedFeasibleRootEightSlot_stabilizer_fixes_root (h : H)
    (hh : h ∈ generatedFifthRootEightLocalAxisStabilizer) (c : ZMod 2) :
    rhoLocal h (conwayShortAxis (Sum.inl (1, 248)) c) = conwayShortAxis (Sum.inl (1, 248)) c := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedFifthRootEightAxis =
      generatedFifthRootEightAxis := by
    rw [hf]
    exact hh
  have hperm := generatedFeasibleRootEightSlot_spatial_root f hfix
  have hcoord := congrFun (generatedFourth_local_short f generatedFifthRootEightAxis)
    (Sum.inl (1, 248))
  rw [hfix] at hcoord
  have himage := localShortOperator_image f (griessConwayEncode generatedFifthRootEightAxis).2.1
    (Sum.inl (1, 248))
  rw [hperm, ← hcoord, generatedFeasibleRootEightSlot_root_coefficient] at himage
  have hq : qSign (localShortPhase f (Sum.inl (1, 248))) = 1 := by linarith
  have hphase := (qSign_eq_one_iff _).mp hq
  rw [← hf, generatedFeasibleFifthSlot_local_image, hperm, hphase, zero_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
