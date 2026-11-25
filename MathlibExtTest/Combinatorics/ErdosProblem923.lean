/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ErdosProblem923

open MathlibExt.Combinatorics.ErdosProblem923Wanted
open SimpleGraph

-- A finite complete graph at the supplied threshold has a triangle-free, non-3-colorable subgraph.
example : ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.CliqueFree 3 ∧ ¬ H.Colorable 3 := by
  obtain ⟨k, hk⟩ := conjecture_holds 4
  obtain ⟨H, _, hχ, hf⟩ := hk (Fin k) ⊤ (by simp)
  exact ⟨k, H, hf, fun hc => (by decide : ¬ (4 : ℕ∞) ≤ 3) (hχ.trans hc.chromaticNumber_le)⟩

-- A countably infinite clique with an isolated vertex meets every finite threshold.
-- The spanning subgraph keeps that vertex isolated.
example (n : ℕ) : ∃ H : SimpleGraph ℕ,
    (n : ℕ∞) ≤ H.chromaticNumber ∧ H.CliqueFree 3 ∧ ∀ v, ¬ H.Adj 0 v := by
  let e : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  let G := (⊤ : SimpleGraph ℕ).map e
  obtain ⟨k, hk⟩ := conjecture_holds n
  have hχ : (k : ℕ∞) ≤ G.chromaticNumber := by
    apply le_trans _ (chromaticNumber_mono_of_hom (Embedding.map e ⊤).toHom)
    simp
  obtain ⟨H, hHG, hH, hf⟩ := hk ℕ G hχ
  refine ⟨H, hH, hf, fun v hv => ?_⟩
  obtain ⟨_, x, _, _, hx, _⟩ := hHG hv
  exact Nat.succ_ne_zero x hx
