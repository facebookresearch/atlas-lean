/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Random.ExpectedCost
import CSLibExt.Algorithms.Lean.Sort.Quick

/-!
# Tests for expected running time

Concrete expected-cost computations over uniform permutations, including
the average comparison count of deterministic quicksort on randomly ordered
inputs of sizes `2` and `3`.
-/

open Cslib.Algorithms.Lean.TimeM
open scoped ENNReal

/-- A constant-time algorithm (always `7` ticks) has expected time `7`
under the uniform permutation of `[1, 2, 3]`. -/
example : expectedTime (fun xs : List ℕ => ⟨xs.head?, 7⟩)
    (uniformPermutation [1, 2, 3]) = (7 : ℝ≥0∞) := by
  have h := expectedTime_uniformPermutation_eq_of_time_eq
    (fun xs : List ℕ => ⟨xs.head?, 7⟩) [1, 2, 3] 7 (fun _ => rfl)
  exact_mod_cast h

/-- Charging one tick per input element gives expected time `4` under the
uniform permutation of `[1, 2, 3, 4]`, since permuting preserves length. -/
example : expectedTime
    (fun xs : List ℕ => (⟨(), xs.length⟩ : Cslib.Algorithms.Lean.TimeM Nat Unit))
    (uniformPermutation [1, 2, 3, 4]) = (4 : ℝ≥0∞) := by
  have h : expectedTime
      (fun xs : List ℕ => (⟨(), xs.length⟩ : Cslib.Algorithms.Lean.TimeM Nat Unit))
      (uniformPermutation [1, 2, 3, 4]) = ((4 : ℕ) : ℝ≥0∞) :=
    expectedTime_uniformPermutation_eq_of_time_eq _ _ 4
      (fun _ => List.length_ofFn)
  exact_mod_cast h

/-- Quicksort on a uniformly random ordering of `[1, 2]` uses `1`
comparison in expectation: each of the two orders costs `1`. -/
example : expectedTime (quickSort (α := ℕ)) (uniformPermutation ([1, 2] : List ℕ)) = 1 := by
  rw [expectedTime_uniformPermutation]
  have hsum : (∑ σ : Equiv.Perm (Fin 2),
      (quickSort (List.ofFn (fun p => ([1, 2] : List ℕ).get (σ p)))).time) =
      2 := by decide
  simp only [List.length_cons, List.length_nil]
  rw [← Nat.cast_sum, hsum]
  norm_num [Nat.factorial]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- Quicksort on a uniformly random ordering of `[1, 2, 3]` uses `8 / 3`
comparisons in expectation: the six orders cost `2, 3, 2, 3, 3, 3` in some
order, totalling `16`, and `16 / 6 = 8 / 3`. Stated via `toReal` through
the bridge lemma, since `8 / 3` is most directly a real number. -/
example : (expectedTime (quickSort (α := ℕ))
    (uniformPermutation ([1, 2, 3] : List ℕ))).toReal = 8 / 3 := by
  rw [expectedTime_uniformPermutation_toReal]
  have hsum : (∑ σ : Equiv.Perm (Fin 3),
      (quickSort (List.ofFn (fun p => ([1, 2, 3] : List ℕ).get (σ p)))).time) =
      16 := by decide
  simp only [List.length_cons, List.length_nil]
  rw [← Nat.cast_sum, hsum]
  norm_num [Nat.factorial]

#print axioms Cslib.Algorithms.Lean.TimeM.expectedTime_uniformPermutation
