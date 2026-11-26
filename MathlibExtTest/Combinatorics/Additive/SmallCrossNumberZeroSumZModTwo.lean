/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Additive.SmallCrossNumberZeroSumZModTwo

open MetaMathlibExt

-- The zero vector is already a good subsequence on its own, even in dimension zero.
example : IsGoodSequence (fun _ : Fin 1 => (0 : Fin 0 → ZMod 2)) := by
  refine ⟨{0}, Finset.singleton_nonempty _, ?_, ?_⟩
  · rw [Finset.sum_singleton]
  · simp only [Finset.sum_singleton, addOrderOf_zero, Nat.cast_one, div_one, le_refl]

-- A repeated nonzero vector has cross number exactly one at the two indices.
example : IsGoodSequence (fun _ : Fin 2 => fun _ : Fin 2 => (1 : ZMod 2)) := by
  let x : Fin 2 → ZMod 2 := fun _ => 1
  have hx : addOrderOf x = 2 := addOrderOf_eq_prime (by decide) (by decide)
  change IsGoodSequence (fun _ : Fin 2 => x)
  exact ⟨Finset.univ, Finset.univ_nonempty, by decide, by norm_num [hx]⟩

-- At ε = 1 the logarithmic correction drops out of the public bound.
example (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s) t) :
    t =O[Filter.atTop] fun d : ℕ => (2 : ℝ) ^ d := by
  simpa using zmod_two_pi_good_threshold_isBigO 1 zero_lt_one t ht
