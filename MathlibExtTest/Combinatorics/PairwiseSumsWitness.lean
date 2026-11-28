/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PairwiseSumsWitness
import MathlibExt.Combinatorics.PairwiseSumTheorem
import MathlibExt.Combinatorics.PartitionRegularUltrafilter

/-! # Tests for ultrafilter witnesses of the pairwise sum family -/

open Filter Set MetaMathlibExt

-- A singleton in a principal ultrafilter cannot contain an infinite set.
example (n : ℕ) : ¬ ∃ W : Ultrafilter (ℕ × ℕ),
    (∀ X ∈ W, ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ k ∈ H, h < k → (h, k) ∈ X) ∧
    W.map Prod.fst = pure n ∧ W.map Prod.snd = pure n ∧ W.map (fun p => p.1 + p.2) = pure n := by
  intro h
  obtain ⟨B, hB, hsub, _⟩ :=
    (pairwiseSums_witness_iff_exists_ramseyWitness (pure n)).2 h {n} (by simp)
  exact hB ((finite_singleton n).subset hsub)

-- The pairwise sum theorem gives a Ramsey witness with all three images equal.
example : ∃ W : Ultrafilter (ℕ × ℕ),
    (∀ X ∈ W, ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ k ∈ H, h < k → (h, k) ∈ X) ∧
    W.map Prod.snd = W.map Prod.fst ∧ W.map (fun p => p.1 + p.2) = W.map Prod.fst := by
  let 𝓕 := {A : Set ℕ | ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
    ∀ b ∈ B, ∀ k ∈ B, b < k → b + k ∈ A}
  obtain ⟨U, hU⟩ := (weaklyPartitionRegular_iff_exists_ultrafilter 𝓕).1 (by
    intro r c
    obtain ⟨B, hB, k, hcolor, hsum⟩ := exists_infinite_pairwiseSums_monochromatic c
    exact ⟨{b | c b = k}, ⟨B, hB, hcolor, fun b hb n hn hbn => hsum b hb n hn hbn.ne⟩,
      k, fun _ h => h⟩)
  obtain ⟨W, hW, hfst, hsnd, hsum⟩ := (pairwiseSums_witness_iff_exists_ramseyWitness U).1 (by
    intro A hA
    obtain ⟨F, ⟨B, hB, hBF, hsum⟩, hFA⟩ := hU A hA
    exact ⟨B, hB, hBF.trans hFA, fun b hb n hn hbn => hFA (hsum b hb n hn hbn)⟩)
  exact ⟨W, hW, hsnd.trans hfst.symm, hsum.trans hfst.symm⟩
