/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPackedAction

/-! A generic finite-cache interface preserves every full-Q phase without expanding long words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original words replay from finite full-Q prefix and original-letter certificates. -/
theorem generatedRootEight_Q_finite_word_replay (w : List (Fin 11)) (l : ℕ)
    (hlen : w.length = l) (letters : ℕ → Fin 11)
    (data : Fin (l + 1) → Fin 24 → ℕ)
    (hl : ∀ n : Fin l, w.reverse.getD n.val 0 = letters n.val)
    (hb : ∀ j, generatedNinthLowerSpinPrimitivePackedQ (data 0 j) = qCoordinateGenerator j)
    (hs : ∀ n : Fin l, ∀ j,
      generatedRootEightQPackedCondition (letters n.val)
        (data (Fin.castAdd 1 n) j) (data ⟨n.val + 1, by omega⟩ j)) (j : Fin 24) :
    generatedRootEightQWordImage w (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ (data ⟨l, by omega⟩ j) := by
  let cache (n : ℕ) := if h : n < l + 1 then data ⟨n, h⟩ j else 0
  have hbase : generatedNinthLowerSpinPrimitivePackedQ (cache 0) = qCoordinateGenerator j := hb j
  have hsteps (n : ℕ) (hn : n < w.reverse.length) :
      generatedRootEightQPackedCondition w.reverse[n] (cache n) (cache (n + 1)) := by
    have hn' : n < l := by simpa only [List.length_reverse, hlen] using hn
    have h := hs ⟨n, hn'⟩ j
    rw [← hl ⟨n, hn'⟩, List.getD_eq_getElem _ _ hn] at h
    have hi : Fin.castAdd 1 (⟨n, hn'⟩ : Fin l) = (⟨n, by omega⟩ : Fin (l + 1)) := by
      apply Fin.ext
      rfl
    rw [hi] at h
    simpa only [cache, show n < l + 1 by omega, show n + 1 < l + 1 by omega,
      ↓reduceDIte] using h
  have h := generatedRootEight_Q_word_replay w cache (qCoordinateGenerator j) hbase hsteps
  simpa only [hlen, cache, show l < l + 1 by omega, ↓reduceDIte] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
