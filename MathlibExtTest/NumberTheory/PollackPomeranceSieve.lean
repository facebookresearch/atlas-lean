/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PollackPomeranceSieve
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum

/-!
# Tests for the Pollack–Pomerance sieve bound
-/

namespace MathlibExtTest.NumberTheory.PollackPomeranceSieve

/-- The same constant works with no excluded primes and with 2 excluded at a nonintegral cutoff. -/
example : ∃ C : ℝ, 0 < C ∧ (∀ x : ℝ, 1 < x → (⌊x⌋₊ : ℝ) ≤ C * x) ∧
    2 ≤ C * (7 / 2) * Real.exp (-(1 / 2)) := by
  classical
  obtain ⟨C, hC, h⟩ := MetaMathlibExt.card_free_of_prime_set_le_exp_neg_sum_inv
  refine ⟨C, hC, fun x hx ↦ ?_, ?_⟩
  · simpa using h ∅ (by simp) x hx
  · have h2 := h {2} (by simpa using Nat.prime_two) (7 / 2) (by norm_num)
    have hfloor : ⌊(7 / 2 : ℝ)⌋₊ = 3 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
    rw [hfloor] at h2
    simp only [Set.mem_singleton_iff, forall_eq] at h2
    have hcount : ((Finset.Icc 1 3).filter (fun n : ℕ ↦ ¬2 ∣ n)).card = 2 := by decide
    have hprimes : ((Finset.Iic 3).filter (fun p : ℕ ↦ p = 2)) = {2} := by decide
    simpa only [hcount, hprimes, Finset.sum_singleton, Nat.cast_ofNat] using h2

end MathlibExtTest.NumberTheory.PollackPomeranceSieve
