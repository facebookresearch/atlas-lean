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

private def consecutive (k : ℕ) (i : Fin k) : ℤ := (i.val : ℤ) + 1

private theorem consecutive_strictMono (k : ℕ) : StrictMono (consecutive k) := by
  intro i j hij
  change i.val < j.val at hij
  unfold consecutive
  omega

private theorem consecutive_pos (k : ℕ) (i : Fin k) : 0 < consecutive k i := by
  unfold consecutive
  omega

-- No terms appended: the lower bound retains the surplus of three on `{1, 2, 3, 4}`.
example : 19 ≤ ((restrictedSignedSumset 3 (orderedFinset (consecutive 4))).card : ℤ) :=
  card_restrictedSignedSumset_ge_of_initialSegment 3 4 (by decide) (by decide)
    (consecutive 4) 3 (consecutive_strictMono 4) (consecutive_pos 4) (by decide) (by decide +kernel)

-- Two extension steps retain that same surplus.
example : 31 ≤ ((restrictedSignedSumset 3 (orderedFinset (consecutive 6))).card : ℤ) :=
  card_restrictedSignedSumset_ge_of_initialSegment 3 6 (by decide) (by decide)
    (consecutive 6) 3 (consecutive_strictMono 6) (consecutive_pos 6) (by decide) (by decide +kernel)

-- A single extension of the first four odd terms attains the lower bound with `t = 0`.
example : 22 ≤ ((restrictedSignedSumset 3
    (orderedFinset fun i : Fin 5 => 2 * (i.val : ℤ) + 1)).card : ℤ) := by
  apply card_restrictedSignedSumset_ge_of_initialSegment 3 5 (by decide) (by decide) _ 0
  · intro i j hij
    change i.val < j.val at hij
    change 2 * (i.val : ℤ) + 1 < 2 * (j.val : ℤ) + 1
    omega
  · intro i
    omega
  · decide
  · decide +kernel
