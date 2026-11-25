/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SparseAdmissiblePowerSets
import Mathlib.Order.Interval.Set.Nat

/-! # Tests for sparse subsets of powers -/

-- A sparsity budget that is zero through `B` excludes the whole initial interval.
-- The same infinite set supplies a witness against the zero shift and any negative shift.
example {a : ℕ}
    (hprim : {p : ℕ | p.Prime ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)}.Infinite)
    (B : ℕ) :
    ∃ A : Set ℕ, A.Infinite ∧ A ∩ Set.Icc 1 B = ∅ ∧
      (∃ m ∈ A, ¬ m.Prime) ∧
      (∀ n : ℤ, n < 0 → ∃ m ∈ A, ¬ ∃ p : ℕ, p.Prime ∧ (p : ℤ) = m + n) := by
  obtain ⟨A, hA, -, hcount, htranslate⟩ :=
    MetaMathlibExt.exists_sparse_subset_pow_no_prime_translate (f := fun N => N - B)
      hprim (fun _ _ h => Nat.sub_le_sub_right h B) (fun M => ⟨M + B, by omega⟩)
  have hfin := (Set.finite_Icc 1 B).subset (Set.inter_subset_right (s := A))
  have hzero : (A ∩ Set.Icc 1 B).ncard = 0 := by simpa using hcount B
  have hbad (n : ℤ) : ∃ m ∈ A, ¬ ∃ p : ℕ, p.Prime ∧ (p : ℤ) = m + n := by
    by_contra h
    exact htranslate ⟨n, fun m hm => by
      by_contra hprime
      exact h ⟨m, hm, hprime⟩⟩
  obtain ⟨m, hm, hm₀⟩ := hbad 0
  refine ⟨A, hA, (Set.ncard_eq_zero hfin).mp hzero, ⟨m, hm, ?_⟩, fun n _ => hbad n⟩
  exact fun hp => hm₀ ⟨m, hp, by simp⟩
