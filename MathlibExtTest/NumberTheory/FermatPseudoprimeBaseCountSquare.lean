/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FermatPseudoprimeBaseCountSquare

/-! # Concrete square counts of Fermat pseudoprime bases -/

namespace MetaMathlibExt

private theorem card_bases_eq_filter_card (n : ℕ) :
    {b : ℕ | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}.ncard =
      ((Finset.range n).filter fun b => 1 ≤ b ∧ Nat.FermatPsp n b).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
  exact and_left_comm

-- Enumerate the bases for 3 * 5 directly: 1, 4, 11, and 14 pass.
example : {b : ℕ | 1 ≤ b ∧ b < 15 ∧ Nat.FermatPsp 15 b}.ncard = 4 := by
  rw [card_bases_eq_filter_card]
  decide +kernel

-- Enumerate the bases for 2 * 3 directly: only 1 passes.
example : {b : ℕ | 1 ≤ b ∧ b < 6 ∧ Nat.FermatPsp 6 b}.ncard = 1 := by
  rw [card_bases_eq_filter_card]
  decide +kernel

example : IsSquare {b : ℕ | 1 ≤ b ∧ b < 15 ∧ Nat.FermatPsp 15 b}.ncard :=
  isSquare_card_fermatPsp_bases_mul_of_prime (p := 3) (q := 5)
    (by decide) (by decide) (by decide)

end MetaMathlibExt
