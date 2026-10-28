/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayData05

/-! Bounded packed certificates for every complete primitive in original root-eight word 5. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 64000000 in
-- Evaluate each original packed primitive at all 24 retained full-Q prefix images.
set_option maxRecDepth 100000 in
-- Replay only literal prefix values, avoiding expansion of the entire nested word.
/-- Every chronological primitive step retains its full original binary and central action. -/
theorem generatedRootEight_Q_replay_05_steps : ∀ n : Fin 34, ∀ j : Fin 24,
    generatedRootEightQPackedCondition (generatedRootEightQReplayLetterLookup05 n.val)
      (generatedRootEightQReplayData05 (Fin.castAdd 1 n) j)
      (generatedRootEightQReplayData05 ⟨n.val + 1, by omega⟩ j) := by
  unfold generatedRootEightQPackedCondition
  decide +kernel

set_option maxRecDepth 100000 in
-- Decode each original full-Q basis prefix including its zero central coefficient.
/-- The first prefix is the original positive Q generator. -/
theorem generatedRootEight_Q_replay_05_base (j : Fin 24) :
    generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData05 0 j) =
      qCoordinateGenerator j := by
  have hb : ∀ i j : Fin 24, toAdd
      (generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData05 0 i)).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
  have hc : ∀ i : Fin 24, toAdd
      (generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData05 0 i)).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact funext (hb j)
  · apply toAdd.injective
    exact hc j

/-- The entire original word has its full-Q image at every basis generator. -/
theorem generatedRootEight_Q_replay_05_actual (j : Fin 24) :
    generatedRootEightQWordImage (generatedRootEightQSourceWords 5) (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData05 34 j) := by
  have hlen : (generatedRootEightQSourceWords 5).length = 34 := by decide +kernel
  let cache (n : ℕ) := if h : n < 35 then generatedRootEightQReplayData05 ⟨n, h⟩ j else 0
  have hb : generatedNinthLowerSpinPrimitivePackedQ (cache 0) = qCoordinateGenerator j :=
    generatedRootEight_Q_replay_05_base j
  have hs (n : ℕ) (hn : n < (generatedRootEightQSourceWords 5).reverse.length) :
      generatedRootEightQPackedCondition (generatedRootEightQSourceWords 5).reverse[n]
        (cache n) (cache (n + 1)) := by
    have hn' : n < 34 := by simpa only [List.length_reverse, hlen] using hn
    have h := generatedRootEight_Q_replay_05_steps ⟨n, hn'⟩ j
    have hl : ∀ n : Fin 34, (generatedRootEightQSourceWords 5).reverse.getD n.val 0 =
        generatedRootEightQReplayLetterLookup05 n.val := by decide +kernel
    rw [← hl ⟨n, hn'⟩, List.getD_eq_getElem _ _ hn] at h
    have hi : Fin.castAdd 1 (⟨n, hn'⟩ : Fin 34) =
        (⟨n, by omega⟩ : Fin 35) := by apply Fin.ext; rfl
    rw [hi] at h
    simpa only [cache, show n < 35 by omega,
      show n + 1 < 35 by omega, ↓reduceDIte] using h
  have h := generatedRootEight_Q_word_replay _ cache _ hb hs
  simpa only [hlen, cache, show 34 < 35 by omega, ↓reduceDIte,
    show (⟨34, by omega⟩ : Fin 35) = 34 by decide] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
