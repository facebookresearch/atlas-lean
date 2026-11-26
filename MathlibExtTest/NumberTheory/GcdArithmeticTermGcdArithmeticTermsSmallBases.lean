/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GcdArithmeticTermGcdArithmeticTermsSmallBases
import MathlibExt.NumberTheory.GcdArithmeticTerm

/-! # Tests for the gcd terms in bases 2, 3 and 4 -/

namespace MathlibExtTest.NumberTheory.GcdArithmeticTermGcdArithmeticTermsSmallBases

open MetaMathlibExt

-- On a non-degenerate pair both identities hold in base 2.
example : (Nat.gcd 2 4 : ℤ) =
    (2 : ℤ) ^ (2 * 4 * (2 * 4 + 2 + 4)) /
      (((2 : ℤ) ^ (2 ^ 2 * 4) - 1) * ((2 : ℤ) ^ (2 * 4 ^ 2) - 1)) %
        (2 : ℤ) ^ (2 * 4) - 1 := by
  have h := (gcd_arithmetic_terms_small_bases 2 (Or.inl rfl) 2 4 (by decide) (by decide)).1
  exact h.mpr (by decide)

example : (Nat.gcd 2 4 : ℤ) =
    (-(2 : ℤ) ^ (2 * 4 * (2 * 4 + 2 + 4))) %
      (((2 : ℤ) ^ (2 ^ 2 * 4) - 1) * ((2 : ℤ) ^ (2 * 4 ^ 2) - 1)) %
        (2 : ℤ) ^ (2 * 4) - 2 := by
  have h := (gcd_arithmetic_terms_small_bases 2 (Or.inl rfl) 2 4 (by decide) (by decide)).2
  exact h.mpr (by decide)

-- On a non-degenerate pair both identities hold in base 3.
example : (Nat.gcd 2 4 : ℤ) =
    (3 : ℤ) ^ (2 * 4 * (2 * 4 + 2 + 4)) /
      (((3 : ℤ) ^ (2 ^ 2 * 4) - 1) * ((3 : ℤ) ^ (2 * 4 ^ 2) - 1)) %
        (3 : ℤ) ^ (2 * 4) - 1 := by
  have h :=
    (gcd_arithmetic_terms_small_bases 3 (Or.inr (Or.inl rfl)) 2 4 (by decide) (by decide)).1
  exact h.mpr (by decide)

example : (Nat.gcd 2 4 : ℤ) =
    (-(3 : ℤ) ^ (2 * 4 * (2 * 4 + 2 + 4))) %
      (((3 : ℤ) ^ (2 ^ 2 * 4) - 1) * ((3 : ℤ) ^ (2 * 4 ^ 2) - 1)) %
        (3 : ℤ) ^ (2 * 4) - 2 := by
  have h :=
    (gcd_arithmetic_terms_small_bases 3 (Or.inr (Or.inl rfl)) 2 4 (by decide) (by decide)).2
  exact h.mpr (by decide)

-- On a non-degenerate pair both identities hold in base 4.
example : (Nat.gcd 2 4 : ℤ) =
    (4 : ℤ) ^ (2 * 4 * (2 * 4 + 2 + 4)) /
      (((4 : ℤ) ^ (2 ^ 2 * 4) - 1) * ((4 : ℤ) ^ (2 * 4 ^ 2) - 1)) %
        (4 : ℤ) ^ (2 * 4) - 1 := by
  have h :=
    (gcd_arithmetic_terms_small_bases 4 (Or.inr (Or.inr rfl)) 2 4 (by decide) (by decide)).1
  exact h.mpr (by decide)

example : (Nat.gcd 2 4 : ℤ) =
    (-(4 : ℤ) ^ (2 * 4 * (2 * 4 + 2 + 4))) %
      (((4 : ℤ) ^ (2 ^ 2 * 4) - 1) * ((4 : ℤ) ^ (2 * 4 ^ 2) - 1)) %
        (4 : ℤ) ^ (2 * 4) - 2 := by
  have h :=
    (gcd_arithmetic_terms_small_bases 4 (Or.inr (Or.inr rfl)) 2 4 (by decide) (by decide)).2
  exact h.mpr (by decide)

-- At (1, 1) both identities fail in base 2.
example : ¬ ((Nat.gcd 1 1 : ℤ) =
    (2 : ℤ) ^ (1 * 1 * (1 * 1 + 1 + 1)) /
      (((2 : ℤ) ^ (1 ^ 2 * 1) - 1) * ((2 : ℤ) ^ (1 * 1 ^ 2) - 1)) %
        (2 : ℤ) ^ (1 * 1) - 1) := by
  have h := (gcd_arithmetic_terms_small_bases 2 (Or.inl rfl) 1 1 le_rfl le_rfl).1
  intro hEq
  exact h.mp hEq rfl

example : ¬ ((Nat.gcd 1 1 : ℤ) =
    (-(2 : ℤ) ^ (1 * 1 * (1 * 1 + 1 + 1))) %
      (((2 : ℤ) ^ (1 ^ 2 * 1) - 1) * ((2 : ℤ) ^ (1 * 1 ^ 2) - 1)) %
        (2 : ℤ) ^ (1 * 1) - 2) := by
  have h := (gcd_arithmetic_terms_small_bases 2 (Or.inl rfl) 1 1 le_rfl le_rfl).2
  intro hEq
  exact h.mp hEq rfl

-- At (1, 1) both identities fail in base 3.
example : ¬ ((Nat.gcd 1 1 : ℤ) =
    (3 : ℤ) ^ (1 * 1 * (1 * 1 + 1 + 1)) /
      (((3 : ℤ) ^ (1 ^ 2 * 1) - 1) * ((3 : ℤ) ^ (1 * 1 ^ 2) - 1)) %
        (3 : ℤ) ^ (1 * 1) - 1) := by
  have h := (gcd_arithmetic_terms_small_bases 3 (Or.inr (Or.inl rfl)) 1 1 le_rfl le_rfl).1
  intro hEq
  exact h.mp hEq rfl

example : ¬ ((Nat.gcd 1 1 : ℤ) =
    (-(3 : ℤ) ^ (1 * 1 * (1 * 1 + 1 + 1))) %
      (((3 : ℤ) ^ (1 ^ 2 * 1) - 1) * ((3 : ℤ) ^ (1 * 1 ^ 2) - 1)) %
        (3 : ℤ) ^ (1 * 1) - 2) := by
  have h := (gcd_arithmetic_terms_small_bases 3 (Or.inr (Or.inl rfl)) 1 1 le_rfl le_rfl).2
  intro hEq
  exact h.mp hEq rfl

-- At (1, 1) both identities fail in base 4.
example : ¬ ((Nat.gcd 1 1 : ℤ) =
    (4 : ℤ) ^ (1 * 1 * (1 * 1 + 1 + 1)) /
      (((4 : ℤ) ^ (1 ^ 2 * 1) - 1) * ((4 : ℤ) ^ (1 * 1 ^ 2) - 1)) %
        (4 : ℤ) ^ (1 * 1) - 1) := by
  have h := (gcd_arithmetic_terms_small_bases 4 (Or.inr (Or.inr rfl)) 1 1 le_rfl le_rfl).1
  intro hEq
  exact h.mp hEq rfl

example : ¬ ((Nat.gcd 1 1 : ℤ) =
    (-(4 : ℤ) ^ (1 * 1 * (1 * 1 + 1 + 1))) %
      (((4 : ℤ) ^ (1 ^ 2 * 1) - 1) * ((4 : ℤ) ^ (1 * 1 ^ 2) - 1)) %
        (4 : ℤ) ^ (1 * 1) - 2) := by
  have h := (gcd_arithmetic_terms_small_bases 4 (Or.inr (Or.inr rfl)) 1 1 le_rfl le_rfl).2
  intro hEq
  exact h.mp hEq rfl

end MathlibExtTest.NumberTheory.GcdArithmeticTermGcdArithmeticTermsSmallBases
