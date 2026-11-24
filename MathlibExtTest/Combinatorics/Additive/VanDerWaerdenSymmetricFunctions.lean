/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenSymmetricFunctions

open MetaMathlibExt

-- For the constant sequence of ones, a zero-sum block has length divisible by the modulus.
example {n : ℕ} (hn : 0 < n) : ∃ l : ℕ, 1 < l ∧ n ∣ l := by
  obtain ⟨l, hl, s, hs⟩ := isVanishingFamily_sum hn 1 Nat.zero_lt_one (fun _ => 1)
  exact ⟨l, hl, (ZMod.natCast_eq_zero_iff l n).mp (by simpa using hs 0 Nat.zero_lt_one)⟩

-- At modulus zero, the same sequence has no zero-sum block of length greater than one.
example : ¬ IsVanishingFamily (fun (l : ℕ) (b : Fin l → ZMod 0) => ∑ i, b i) := by
  intro h
  obtain ⟨l, hl, s, hs⟩ := h 1 Nat.zero_lt_one (fun _ => 1)
  have hzero : (l : ZMod 0) = 0 := by simpa using hs 0 Nat.zero_lt_one
  have := (ZMod.natCast_eq_zero_iff l 0).mp hzero
  simp_all

-- The empty block has sum zero and product one.
example {n : ℕ} (c : ZMod n) (b : Fin 0 → ZMod n) : sumAddMulProdFamily c 0 b = c := by
  simp [sumAddMulProdFamily]

-- On the constant sequence of ones the product stays one, so six must divide the length plus one.
example : ∃ l : ℕ, 1 < l ∧ 6 ∣ l + 1 := by
  obtain ⟨l, hl, s, hs⟩ := isMVanishingFamily_one_sumAddMulProd_one_six (fun _ => 1)
  exact ⟨l, hl, (ZMod.natCast_eq_zero_iff (l + 1) 6).mp
    (by simpa [sumAddMulProdFamily] using hs 0 Nat.zero_lt_one)⟩

-- The adjacent residues 1 and 5 have zero sum, but their sum plus product is 5.
example : sumAddMulProdFamily (1 : ZMod 6) 2 (fun i => if i = 0 then 1 else 5) = 5 := by
  rw [sumAddMulProdFamily_two]
  decide
