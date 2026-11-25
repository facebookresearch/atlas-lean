/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PowerFreeParity

/-!
# Tests for odd-to-even ratios of power-free integers
-/

open Filter Topology MetaMathlibExt

-- At the lowest exponent, the statement specializes to the odd-to-even ratio of squarefrees.
example : Tendsto (fun N : ℕ =>
    ({n : ℕ | n ≤ N ∧ Squarefree n ∧ Odd n}.ncard : ℝ) /
      {n : ℕ | n ≤ N ∧ Squarefree n ∧ Even n}.ncard) atTop (𝓝 2) := by
  have h (n : ℕ) (P : Prop) : (n ≠ 0 ∧ Squarefree n ∧ P) ↔ Squarefree n ∧ P :=
    ⟨And.right, fun hn => ⟨hn.1.ne_zero, hn⟩⟩
  simpa only [Nat.isKFull_k_eq_one, Nat.isPowerFree_two, h,
    show (2 : ℝ) ^ 2 / (2 ^ 2 - 2) = 2 by norm_num] using
    tendsto_card_odd_lFree_div_card_even_lFree (l := 2) (hl := by decide)

-- Cubefree integers include multiples of four, and have a different limiting ratio.
example : Tendsto (fun N : ℕ =>
    ({n : ℕ | n ≤ N ∧ Nat.IsKFull 1 n ∧ n.IsPowerFree 3 ∧ Odd n}.ncard : ℝ) /
      {n : ℕ | n ≤ N ∧ Nat.IsKFull 1 n ∧ n.IsPowerFree 3 ∧ Even n}.ncard)
    atTop (𝓝 (4 / 3 : ℝ)) := by
  convert tendsto_card_odd_lFree_div_card_even_lFree (l := 3) (by decide) using 2
  norm_num

-- The even count already has a witness at the endpoint N = 2, for every allowed exponent.
example {l N : ℕ} (hl : 2 ≤ l) (hN : 2 ≤ N) :
    2 ∈ {n : ℕ | n ≤ N ∧ Nat.IsKFull 1 n ∧ n.IsPowerFree l ∧ Even n} := by
  exact ⟨hN, Nat.isKFull_k_eq_one.mpr (by decide),
    (Nat.isPowerFree_two.mpr (Nat.prime_iff.mp Nat.prime_two).squarefree).mono hl,
    even_iff_two_dvd.mpr dvd_rfl⟩
