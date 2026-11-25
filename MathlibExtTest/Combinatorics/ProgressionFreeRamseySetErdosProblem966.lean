/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ProgressionFreeRamseySetErdosProblem966
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Small cases of progression-free Ramsey sets (Erdős Problem 966)

For `k = 2` the set contains no three-term progression `x, x + d, x + 2 d` with `d > 0`, and every
two-colouring of it has two distinct elements of the same colour. Numeral lengths can be read off
the theorem directly.
-/

namespace MathlibExtTest.Combinatorics.ProgressionFreeRamseySetErdosProblem966

open MathlibExt.Combinatorics.ProgressionFreeRamseySetErdosProblem966Wanted

-- `x, x + d, x + 2 d` with `d > 0` is an arithmetic progression of length three.
private theorem isAPOfLength_three {x d : ℕ} (hd : 0 < d) :
    ({x, x + d, x + 2 * d} : Set ℕ).IsAPOfLength 3 := by
  refine ⟨x, d, ?_, ?_⟩
  · rw [ENat.card_coe_set_eq, Set.encard_insert_of_notMem (by simp; omega),
      Set.encard_insert_of_notMem (by simp; omega), Set.encard_singleton]
    rfl
  · ext y
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by simp⟩
    · rintro ⟨n, hn, rfl⟩
      have hn' : n < 3 := by exact_mod_cast hn
      interval_cases n <;> simp

-- With `k = 2`, the progression-free condition excludes genuine three-term progressions, and the
-- monochromatic two-term progression consists of two distinct elements.
example : ∃ A : Set ℕ, (∀ x d : ℕ, 0 < d → ¬ ({x, x + d, x + 2 * d} : Set ℕ) ⊆ A) ∧
    ∀ c : ℕ → Fin 2, ∃ y ∈ A, ∃ z ∈ A, y ≠ z ∧ c y = c z := by
  obtain ⟨A, hfree, hmono⟩ := progressionFreeRamseySet_holds 2 2 le_rfl le_rfl
  refine ⟨A, fun x d hd hsub => ?_, fun c => ?_⟩
  · have h3 : ((2 : ℕ) : ℕ∞) + 1 = 3 := by norm_num
    rw [h3] at hfree
    have := hfree _ hsub (isAPOfLength_three hd)
    norm_num at this
  · obtain ⟨t, htA, ⟨a, d, hcard, rfl⟩, i, hi⟩ := hmono c
    have h0 : a + 0 • d ∈ {x | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < (2 : ℕ)), a + n • d = x} :=
      ⟨0, by norm_num, rfl⟩
    have h1 : a + 1 • d ∈ {x | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < (2 : ℕ)), a + n • d = x} :=
      ⟨1, by norm_num, rfl⟩
    refine ⟨_, htA h0, _, htA h1, fun h => ?_, (hi _ h0).trans (hi _ h1).symm⟩
    -- Equal terms force difference zero, and then the progression has a single element.
    have hd : d = 0 := by simpa using h
    subst hd
    have hset : {x | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < (2 : ℕ)), a + n • 0 = x} = {a} := by
      ext x
      simp only [smul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun ⟨_, _, hx⟩ => hx.symm, fun hx => ⟨0, by norm_num, hx.symm⟩⟩
    rw [hset, ENat.card_coe_set_eq, Set.encard_singleton] at hcard
    norm_num at hcard

-- Numeral lengths: four-term-progression-free sets that are Ramsey for three-term progressions.
example : ∃ A : Set ℕ, A.IsAPOfLengthFree 4 ∧
    ∀ c : ℕ → Fin 3, ∃ t ⊆ A, t.IsAPOfLength 3 ∧ ∃ i : Fin 3, ∀ x ∈ t, c x = i := by
  have h4 : (3 : ℕ∞) + 1 = 4 := by norm_num
  have h := progressionFreeRamseySet_holds 3 3 (by norm_num) (by norm_num)
  simpa only [Nat.cast_ofNat, h4] using h

end MathlibExtTest.Combinatorics.ProgressionFreeRamseySetErdosProblem966
