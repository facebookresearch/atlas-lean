/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayData04

/-! Bounded packed certificates for every complete primitive in original root-eight word 4. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 64000000 in
-- Evaluate each original packed primitive at all 24 retained full-Q prefix images.
set_option maxRecDepth 100000 in
-- Replay only literal prefix values, avoiding expansion of the entire nested word.
/-- Every chronological primitive step retains its full original binary and central action. -/
theorem generatedRootEight_Q_replay_04_steps : ∀ n : Fin 20, ∀ j : Fin 24,
    generatedRootEightQPackedCondition (generatedRootEightQReplayLetterLookup04 n.val)
      (generatedRootEightQReplayData04 (Fin.castAdd 1 n) j)
      (generatedRootEightQReplayData04 ⟨n.val + 1, by omega⟩ j) := by
  unfold generatedRootEightQPackedCondition
  decide +kernel

set_option maxRecDepth 100000 in
-- Decode each original full-Q basis prefix including its zero central coefficient.
/-- The first prefix is the original positive Q generator. -/
theorem generatedRootEight_Q_replay_04_base (j : Fin 24) :
    generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData04 0 j) =
      qCoordinateGenerator j := by
  have hb : ∀ i j : Fin 24, toAdd
      (generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData04 0 i)).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
  have hc : ∀ i : Fin 24, toAdd
      (generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData04 0 i)).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact funext (hb j)
  · apply toAdd.injective
    exact hc j

/-- The entire original word has its full-Q image at every basis generator. -/
theorem generatedRootEight_Q_replay_04_actual (j : Fin 24) :
    generatedRootEightQWordImage (generatedRootEightQSourceWords 4) (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData04 20 j) := by
  have hlen : (generatedRootEightQSourceWords 4).length = 20 := by decide +kernel
  let cache (n : ℕ) := if h : n < 21 then generatedRootEightQReplayData04 ⟨n, h⟩ j else 0
  have hb : generatedNinthLowerSpinPrimitivePackedQ (cache 0) = qCoordinateGenerator j :=
    generatedRootEight_Q_replay_04_base j
  have hs (n : ℕ) (hn : n < (generatedRootEightQSourceWords 4).reverse.length) :
      generatedRootEightQPackedCondition (generatedRootEightQSourceWords 4).reverse[n]
        (cache n) (cache (n + 1)) := by
    have hn' : n < 20 := by simpa only [List.length_reverse, hlen] using hn
    have h := generatedRootEight_Q_replay_04_steps ⟨n, hn'⟩ j
    have hl : ∀ n : Fin 20, (generatedRootEightQSourceWords 4).reverse.getD n.val 0 =
        generatedRootEightQReplayLetterLookup04 n.val := by decide +kernel
    rw [← hl ⟨n, hn'⟩, List.getD_eq_getElem _ _ hn] at h
    have hi : Fin.castAdd 1 (⟨n, hn'⟩ : Fin 20) =
        (⟨n, by omega⟩ : Fin 21) := by apply Fin.ext; rfl
    rw [hi] at h
    simpa only [cache, show n < 21 by omega,
      show n + 1 < 21 by omega, ↓reduceDIte] using h
  have h := generatedRootEight_Q_word_replay _ cache _ hb hs
  simpa only [hlen, cache, show 20 < 21 by omega, ↓reduceDIte,
    show (⟨20, by omega⟩ : Fin 21) = 20 by decide] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
