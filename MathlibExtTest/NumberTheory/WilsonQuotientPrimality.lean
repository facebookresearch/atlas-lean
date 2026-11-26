/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WilsonQuotientPrimality

open MathlibExt.NumberTheory.WilsonQuotientsWanted

-- The unit modulus and the empty shifted product at `n = 2` both give a zero residue.
example : ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 1 ∧ z ≡ 0 [ZMOD 1] := by
  obtain ⟨z, hz, hmod⟩ :=
    exists_int_eq_wilsonQuotientZ_two_mul_sub_one_modEq_zero_iff 1 (by decide)
  exact ⟨z, hz, hmod.mpr (Or.inl rfl)⟩

example : ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 3 ∧ z ≡ 0 [ZMOD 2] := by
  obtain ⟨z, hz, hmod⟩ :=
    exists_int_eq_wilsonQuotientZ_two_mul_sub_one_modEq_zero_iff 2 (by decide)
  exact ⟨z, hz, hmod.mpr (Or.inr (by decide))⟩

example : ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 9 ∧ z ≡ 0 [ZMOD 5] := by
  obtain ⟨z, hz, hmod⟩ :=
    exists_int_eq_wilsonQuotientZ_two_mul_sub_one_modEq_zero_iff 5 (by decide)
  exact ⟨z, hz, hmod.mpr (Or.inr (by decide))⟩

-- The factorial quotient is 180 at `n = 4`, and adding one gives a nonzero residue.
example : wilsonQuotientZ 7 = 181 := by
  unfold wilsonQuotientZ wilsonQuotientM
  decide +kernel

example : ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 7 ∧ ¬(z ≡ 0 [ZMOD 4]) := by
  obtain ⟨z, hz, hmod⟩ :=
    exists_int_eq_wilsonQuotientZ_two_mul_sub_one_modEq_zero_iff 4 (by decide)
  exact ⟨z, hz, hmod.not.mpr (by decide)⟩

example : (∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 1) ∧ wilsonQuotientZ 1 = 2 := by
  refine ⟨exists_int_eq_wilsonQuotientZ (n := 1) (hn := by decide), ?_⟩
  unfold wilsonQuotientZ wilsonQuotientM
  decide +kernel

-- The even and odd composite cases have different values.
example : (∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 4) ∧ wilsonQuotientZ 4 = 1 := by
  refine ⟨exists_int_eq_wilsonQuotientZ (n := 4) (hn := by decide), ?_⟩
  unfold wilsonQuotientZ wilsonQuotientM
  decide +kernel

example : (∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 9) ∧ wilsonQuotientZ 9 = 8065 := by
  refine ⟨exists_int_eq_wilsonQuotientZ (n := 9) (hn := by decide), ?_⟩
  unfold wilsonQuotientZ wilsonQuotientM
  decide +kernel
