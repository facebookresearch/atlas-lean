/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

@[expose] public section

open MetaMathlibExt

-- Boundary: the zero-fold sumsets are `{0}`, the empty sum.
example : restrictedSumset 0 ({1, 2, 3} : Finset ℤ) = {0} := by decide
example : restrictedSignedSumset 0 ({1, 2, 3} : Finset ℤ) = {0} := by decide

-- Boundary: more summands than elements gives the empty set.
example : restrictedSumset 4 ({1, 2, 3} : Finset ℤ) = ∅ := by decide
example : restrictedSignedSumset 4 ({1, 2, 3} : Finset ℤ) = ∅ := by decide

-- Distinct summands: `2^∧ {1, 2, 3} = {3, 4, 5}` (no `1 + 1` or `3 + 3`).
example : restrictedSumset 2 ({1, 2, 3} : Finset ℤ) = {3, 4, 5} := by decide

-- Signs: `1^∧_± {1, 2} = {-2, -1, 1, 2}` and `2^∧_± {1, 2} = {-3, -1, 1, 3}`.
example : restrictedSignedSumset 1 ({1, 2} : Finset ℤ) = {-2, -1, 1, 2} := by decide
example : restrictedSignedSumset 2 ({1, 2} : Finset ℤ) = {-3, -1, 1, 3} := by decide

-- The coefficient characterization rejects a repeated summand: `2 ∉ 2^∧ {1, 3}`.
example : (2 : ℤ) ∉ restrictedSumset 2 ({1, 3} : Finset ℤ) := by decide

-- Semantic check through the membership lemma: coefficient `-1` on `2` and `1` on `3`.
example : (1 : ℤ) ∈ restrictedSignedSumset 2 ({2, 3} : Finset ℤ) := by
  rw [mem_restrictedSignedSumset_iff]
  refine ⟨fun a => if a = 2 then -1 else if a = 3 then 1 else 0, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp
  · decide
  · decide
