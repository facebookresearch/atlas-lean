/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.GaussClassNumberTotient
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the totient lower bounds for Gauss class numbers

The bounds of `MetaMathlibExt.gaussClassNumber_mul_totient_le` at small discriminants, with the
class numbers computed by `decide`. At $D = -3$ and $f = 7$ the second bound is an equality:
$\varphi(7) = 6 = 3\, h(-147)$.
-/

namespace MetaMathlibExt.GaussClassNumberTotientTest

open ImaginaryQuadraticDiscriminant

theorem fundamental_neg_seven : IsFundamentalImaginaryQuadraticDiscriminant (-7) :=
  ⟨by norm_num, Or.inl ⟨(Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree, by decide⟩⟩

theorem fundamental_neg_three : IsFundamentalImaginaryQuadraticDiscriminant (-3) :=
  ⟨by norm_num, Or.inl ⟨(Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree, by decide⟩⟩

theorem fundamental_neg_four : IsFundamentalImaginaryQuadraticDiscriminant (-4) :=
  ⟨by norm_num, Or.inr ⟨-1, by norm_num, by simp, by decide⟩⟩

-- `h(-7) φ(3) ≤ h(-63)`, from the first bound.
example : gaussClassNumber (-7) * Nat.totient 3 ≤ gaussClassNumber ((3 : ℕ) ^ 2 * (-7)) :=
  (gaussClassNumber_mul_totient_le fundamental_neg_seven (by norm_num)).1 (by norm_num)
    (by norm_num)

-- The computed values: `h(-7) = 1`, `φ(3) = 2` and `h(-63) = 4`.
example : gaussClassNumber (-7) = 1 ∧ Nat.totient 3 = 2 ∧ gaussClassNumber (-63) = 4 := by
  refine ⟨by decide +kernel, by decide, by decide +kernel⟩

-- `φ(7) ≤ 3 h(-147)`, from the second bound; here `h(-147) = 2`, so equality holds.
example : Nat.totient 7 ≤ 3 * gaussClassNumber ((7 : ℕ) ^ 2 * (-3)) :=
  (gaussClassNumber_mul_totient_le fundamental_neg_three (by norm_num)).2 (Or.inl rfl)

example : Nat.totient 7 = 6 ∧ gaussClassNumber (-147) = 2 := by
  refine ⟨by decide, by decide +kernel⟩

-- `φ(5) ≤ 3 h(-100)` at `D = -4`; here `h(-100) = 2`.
example : Nat.totient 5 ≤ 3 * gaussClassNumber ((5 : ℕ) ^ 2 * (-4)) :=
  (gaussClassNumber_mul_totient_le fundamental_neg_four (by norm_num)).2 (Or.inr rfl)

example : gaussClassNumber (-100) = 2 := by decide +kernel

-- At `f = 1` the first bound reads `h(D) ≤ h(D)`.
example : gaussClassNumber (-7) * Nat.totient 1 ≤ gaussClassNumber ((1 : ℕ) ^ 2 * (-7)) :=
  (gaussClassNumber_mul_totient_le fundamental_neg_seven le_rfl).1 (by norm_num) (by norm_num)

end MetaMathlibExt.GaussClassNumberTotientTest
