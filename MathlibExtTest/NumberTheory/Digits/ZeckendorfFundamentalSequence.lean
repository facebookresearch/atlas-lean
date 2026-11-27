/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ZeckendorfFundamentalSequence

/-! # Tests for the Zeckendorf fundamental sequence -/

open MetaMathlibExt

private abbrev Support := {s : Finset ℕ // ∀ k ∈ s, k + 1 ∉ s}

private theorem fib_bijective :
    Function.Bijective (fun s : Support => ∑ k ∈ s.val, Nat.fib (k + 2)) :=
  (bijective_nonadjacent_finset_sum_iff_eq_fib (fun k => Nat.fib_pos.mpr (by omega))
    Nat.fib_add_two_strictMono).2 fun _ => rfl

-- Zero has the empty support.
example (s : Support) (hs : ∑ k ∈ s.val, Nat.fib (k + 2) = 0) : s.val = ∅ := by
  let t : Support := ⟨∅, by simp⟩
  exact congrArg Subtype.val (fib_bijective.injective (a₁ := s) (a₂ := t) (by simpa [t] using hs))

-- Four uses indices zero and two, the smallest permitted gap.
example (s : Support) (hs : ∑ k ∈ s.val, Nat.fib (k + 2) = 4) : s.val = {0, 2} := by
  let t : Support := ⟨{0, 2}, by simp⟩
  apply congrArg Subtype.val (a₂ := t)
  apply fib_bijective.injective
  exact hs.trans (by decide)

-- The sequence 1, 2, 3, 4, … first differs from the required weights at index three.
example : ¬ Function.Bijective (fun s : Support => ∑ k ∈ s.val, (k + 1)) := by
  intro h
  have heq := (bijective_nonadjacent_finset_sum_iff_eq_fib Nat.succ_pos
    (fun _ _ hlt => Nat.succ_lt_succ hlt)).1 h 3
  exact (by decide : 4 ≠ Nat.fib (3 + 2)) heq
