/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.MPTQSets
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The pairing 1 · 6 = 2 · 3 satisfies every hypothesis.
example : (1 : ℝ) * 3 ≠ 6 * 2 ∧ (1 : ℝ) * 2 ≠ 6 * 3 := by
  apply mul_ne_of_mul_eq_of_distinct (ha := ?_) (hab := ?_) (hbc := ?_)
    (hbd := ?_) (hcd := ?_) <;> norm_num

example : ¬ IsMPTQSet ({1} : Finset ℝ) :=
  not_isMPTQSet_singleton 1

example (x : ℝ) : ¬ IsMPTQSet {0, x} :=
  not_isMPTQSet_of_zero_mem (by simp)

open scoped Pointwise in
example : ¬ IsMPTQSet (({1} : Finset ℝ) ∪ -{1}) := by
  have hpos : ∀ a ∈ ({1} : Finset ℝ), 0 < a := by simp
  exact mt (isMPTQSet_union_neg_iff hpos).mp (not_isMPTQSet_singleton 1)

-- The rational valuation argument also covers signed sets.
example :
    IsMPTQSet ((({-3, 1} : Finset ℤ) ∪ ({-3, 1} : Finset ℤ).image ((2 : ℤ) * ·)).image
      ((↑) : ℤ → ℝ)) ↔ IsMPTQSet (({-3, 1} : Finset ℤ).image ((↑) : ℤ → ℝ)) := by
  apply isMPTQSet_union_prime_mul_iff _ (p := 2) Nat.prime_two
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨1, 2, by norm_num⟩
  · exact ⟨1, 0, by norm_num⟩

-- The three copies can all be empty; the proof need not assume the original set is inhabited.
example : ¬ IsMPTQSet (∅ : Finset ℝ) := by
  have h := isMPTQSet_union_prime_mul_iff (∅ : Finset ℤ) (p := 2) Nat.prime_two (by simp)
  have hn : ¬ IsMPTQSet ((∅ : Finset ℤ).image ((↑) : ℤ → ℝ)) := by simp [IsMPTQSet]
  simpa using mt h.mp hn
