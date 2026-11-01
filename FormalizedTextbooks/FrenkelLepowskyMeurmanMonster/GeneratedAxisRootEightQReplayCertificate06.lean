/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayData06

/-! Bounded packed certificates for every complete primitive in original root-eight word 6. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 64000000 in
-- Evaluate each original packed primitive at all 24 retained full-Q prefix images.
set_option maxRecDepth 100000 in
-- Replay only literal prefix values, avoiding expansion of the entire nested word.
/-- Every chronological primitive step retains its full original binary and central action. -/
theorem generatedRootEight_Q_replay_06_steps : ∀ n : Fin 47, ∀ j : Fin 24,
    generatedRootEightQPackedCondition (generatedRootEightQReplayLetterLookup06 n.val)
      (generatedRootEightQReplayData06 (Fin.castAdd 1 n) j)
      (generatedRootEightQReplayData06 ⟨n.val + 1, by omega⟩ j) := by
  unfold generatedRootEightQPackedCondition
  decide +kernel

set_option maxRecDepth 100000 in
-- Decode each original full-Q basis prefix including its zero central coefficient.
/-- The first prefix is the original positive Q generator. -/
theorem generatedRootEight_Q_replay_06_base (j : Fin 24) :
    generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData06 0 j) =
      qCoordinateGenerator j := by
  have hb : ∀ i j : Fin 24, toAdd
      (generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData06 0 i)).base j =
        toAdd (qCoordinateGenerator i).base j := by decide +kernel
  have hc : ∀ i : Fin 24, toAdd
      (generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData06 0 i)).coeff =
        toAdd (qCoordinateGenerator i).coeff := by decide +kernel
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact funext (hb j)
  · apply toAdd.injective
    exact hc j

/-- The entire original word has its full-Q image at every basis generator. -/
theorem generatedRootEight_Q_replay_06_actual (j : Fin 24) :
    generatedRootEightQWordImage (generatedRootEightQSourceWords 6) (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ (generatedRootEightQReplayData06 47 j) := by
  have hlen : (generatedRootEightQSourceWords 6).length = 47 := by decide +kernel
  let cache (n : ℕ) := if h : n < 48 then generatedRootEightQReplayData06 ⟨n, h⟩ j else 0
  have hb : generatedNinthLowerSpinPrimitivePackedQ (cache 0) = qCoordinateGenerator j :=
    generatedRootEight_Q_replay_06_base j
  have hs (n : ℕ) (hn : n < (generatedRootEightQSourceWords 6).reverse.length) :
      generatedRootEightQPackedCondition (generatedRootEightQSourceWords 6).reverse[n]
        (cache n) (cache (n + 1)) := by
    have hn' : n < 47 := by simpa only [List.length_reverse, hlen] using hn
    have h := generatedRootEight_Q_replay_06_steps ⟨n, hn'⟩ j
    have hl : ∀ n : Fin 47, (generatedRootEightQSourceWords 6).reverse.getD n.val 0 =
        generatedRootEightQReplayLetterLookup06 n.val := by decide +kernel
    rw [← hl ⟨n, hn'⟩, List.getD_eq_getElem _ _ hn] at h
    have hi : Fin.castAdd 1 (⟨n, hn'⟩ : Fin 47) =
        (⟨n, by omega⟩ : Fin 48) := by apply Fin.ext; rfl
    rw [hi] at h
    simpa only [cache, show n < 48 by omega,
      show n + 1 < 48 by omega, ↓reduceDIte] using h
  have h := generatedRootEight_Q_word_replay _ cache _ hb hs
  simpa only [hlen, cache, show 47 < 48 by omega, ↓reduceDIte,
    show (⟨47, by omega⟩ : Fin 48) = 47 by decide] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
