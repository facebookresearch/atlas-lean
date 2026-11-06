/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayData11

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Bounded packed certificates for every complete primitive in original root-eight word 11. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 64000000 in
-- Evaluate each original packed primitive at all 24 retained full-Q prefix images.
set_option maxRecDepth 100000 in
-- Replay only literal prefix values, avoiding expansion of the entire nested word.
/-- Every chronological primitive step retains its full original binary and central action. -/
theorem generatedRootEight_Q_replay_11_steps : ∀ n : Fin 10, ∀ j : Fin 24,
    generatedRootEightQPackedCondition (generatedRootEightQReplayLetterLookup11 n.val)
      (generatedRootEightQReplayData11 (Fin.castAdd 1 n) j)
      (generatedRootEightQReplayData11 ⟨n.val + 1, by omega⟩ j) := by
  unfold generatedRootEightQPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central]
  decide +kernel

set_option maxRecDepth 100000 in
-- Decode each original full-Q basis prefix including its zero central coefficient.
/-- The first prefix is the original positive Q generator. -/
theorem generatedRootEight_Q_replay_11_base (j : Fin 24) :
    generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData11 0 j) =
      qCoordinateGenerator j := by
  have hb : ∀ i j : Fin 24, toAdd
      (generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData11 0 i)).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
  have hc : ∀ i : Fin 24, toAdd
      (generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData11 0 i)).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact funext (hb j)
  · apply toAdd.injective
    exact hc j

set_option maxHeartbeats 64000000 in
-- Compare all original chronological letters with their exact bounded source lookup.
set_option maxRecDepth 100000 in
-- Check the finite original-word addresses once outside the full-Q replay proof.
/-- Every cached chronological letter is exactly the original source word letter. -/
theorem generatedRootEight_Q_replay_11_letters : ∀ n : Fin 10,
    (generatedRootEightQSourceWords 11).reverse.getD n.val 0 =
    generatedRootEightQReplayLetterLookup11 n.val := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
