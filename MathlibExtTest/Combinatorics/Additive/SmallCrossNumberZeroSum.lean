/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Additive.SmallCrossNumberZeroSum

open MetaMathlibExt

-- A sequence of length zero has no nonempty witness.
example : goodSequenceProb (ZMod 35) 0 = 0 := by
  have h : {g : Fin 0 → ZMod 35 | IsGoodSequence g} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, ⟨i, -⟩, -⟩
    exact i.elim0
  simp [goodSequenceProb, h]

-- Two copies of the nonzero element of order two attain cross number exactly one.
example : IsGoodSequence (fun _ : Fin 2 => (1 : ZMod 2)) := by
  refine ⟨Finset.univ, Finset.univ_nonempty, ?_, ?_⟩
  · decide
  · norm_num [ZMod.addOrderOf_one]

-- At length one in `ZMod 2 ^ 1`, only the zero sequence is good.
example : goodSequenceProb (Fin 1 → ZMod 2) 1 = 1 / 2 := by
  have h : {g : Fin 1 → Fin 1 → ZMod 2 | IsGoodSequence g} = {0} := by
    ext g
    change IsGoodSequence g ↔ g = 0
    constructor
    · rintro ⟨s, ⟨i, hi⟩, hz, -⟩
      have hs : s = {i} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j _ => Subsingleton.elim j i⟩
      rw [hs, Finset.sum_singleton] at hz
      funext j
      rw [Subsingleton.elim j i]
      exact hz
    · rintro rfl
      exact ⟨{0}, Finset.singleton_nonempty _, by simp, by simp⟩
  simp [goodSequenceProb, h]

-- The threshold bound for good sequences in `ZMod 2 ^ d`.
example (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s) t) :
    t =O[Filter.atTop]
      fun d : ℕ => (2 : ℝ) ^ d / Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) ^ (1 - ε) :=
  zmod_two_pi_good_threshold_isBigO ε hε t ht

-- At length one in the group of order 35, only the zero sequence is good.
example : goodSequenceProb (ZMod 35) 1 = 1 / 35 := by
  have h : {g : Fin 1 → ZMod 35 | IsGoodSequence g} = {0} := by
    ext g
    change IsGoodSequence g ↔ g = 0
    constructor
    · rintro ⟨s, ⟨i, hi⟩, hz, -⟩
      have hs : s = {i} := Finset.ext fun j => by simp [Subsingleton.elim j i, hi]
      rw [hs, Finset.sum_singleton] at hz
      funext j
      simpa [Subsingleton.elim j i] using hz
    · rintro rfl
      exact ⟨{0}, Finset.singleton_nonempty _, by simp, by simp⟩
  simp [goodSequenceProb, h]
