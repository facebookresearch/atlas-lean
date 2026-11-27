/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.AmbiguousReducedForms
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Simproc.Factors

/-!
# Tests for `BinaryQuadraticForm.ncard_ambiguous_reduced_forms`

The three shapes of ambiguous reduced forms, and each case of Oesterlé's formula (9) at small
discriminants, including the edge case $d = 4$ and the imprimitive form $2x^2 + 2xy + 2y^2$ of
discriminant $-12$, which is not counted.
-/

namespace BinaryQuadraticForm.AmbiguousReducedFormsTest

-- `x² + xy + y²` (discriminant `-3`) has `b = a` and `a = c`.
example : IsGaussReduced 1 1 1 ∧ discrim (1 : ℤ) 1 1 = -3 ∧
    Int.gcd (Int.gcd 1 1 : ℤ) 1 = 1 := by
  unfold IsGaussReduced
  decide

-- `x² + 8y²` (discriminant `-32`) has `b = 0`.
example : IsGaussReduced 1 0 8 ∧ discrim (1 : ℤ) 0 8 = -32 ∧
    Int.gcd (Int.gcd 1 0 : ℤ) 8 = 1 := by
  unfold IsGaussReduced
  decide

-- `3x² + 2xy + 3y²` (discriminant `-32`) has `a = c`; its opposite is not reduced.
example : IsGaussReduced 3 2 3 ∧ discrim (3 : ℤ) 2 3 = -32 ∧
    Int.gcd (Int.gcd 3 2 : ℤ) 3 = 1 := by
  unfold IsGaussReduced
  decide

example : ¬ IsGaussReduced 3 (-2) 3 := by
  unfold IsGaussReduced
  decide

-- `2x² + 2xy + 3y²` (discriminant `-20`) has `b = a`.
example : IsGaussReduced 2 2 3 ∧ discrim (2 : ℤ) 2 3 = -20 ∧
    Int.gcd (Int.gcd 2 2 : ℤ) 3 = 1 := by
  unfold IsGaussReduced
  decide

-- `2x² + 2xy + 2y²` (discriminant `-12`) is reduced but not primitive.
example : IsGaussReduced 2 2 2 ∧ discrim (2 : ℤ) 2 2 = -12 ∧
    Int.gcd (Int.gcd 2 2 : ℤ) 2 = 2 := by
  unfold IsGaussReduced
  decide

-- `d = 3`, odd: `2 ^ (t - 1) = 1`.
example : {q : ℤ × ℤ × ℤ | IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = -3 ∧
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
    (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)}.ncard = 1 := by
  have h := (ncard_ambiguous_reduced_forms 3 (by norm_num) (by norm_num)).1
    (by norm_num) (by norm_num)
  simpa [Nat.primeFactors, Nat.primeFactorsList_ofNat] using h

-- `d = 15`, odd: `2 ^ (t - 1) = 2`, the forms `x² + xy + 4y²` and `2x² + xy + 2y²`.
example : {q : ℤ × ℤ × ℤ | IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = -15 ∧
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
    (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)}.ncard = 2 := by
  have h := (ncard_ambiguous_reduced_forms 15 (by norm_num) (by norm_num)).1
    (by norm_num) (by norm_num)
  simpa [Nat.primeFactors, Nat.primeFactorsList_ofNat] using h

-- `d = 4 ≡ 4 (mod 16)`: `2 ^ (t - 1) = 1`, the form `x² + y²`.
example : {q : ℤ × ℤ × ℤ | IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = -4 ∧
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
    (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)}.ncard = 1 := by
  have h := (ncard_ambiguous_reduced_forms 4 (by norm_num) (by norm_num)).1
    (by norm_num) (by norm_num)
  simpa [Nat.primeFactors, Nat.primeFactorsList_ofNat] using h

-- `d = 12 ≡ 12 (mod 16)`: `2 ^ (t - 2) = 1`, the form `x² + 3y²`.
example : {q : ℤ × ℤ × ℤ | IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = -12 ∧
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
    (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)}.ncard = 1 := by
  have h := (ncard_ambiguous_reduced_forms 12 (by norm_num) (by norm_num)).2.1 (by norm_num)
  simpa [Nat.primeFactors, Nat.primeFactorsList_ofNat] using h

-- `d = 60 ≡ 12 (mod 16)`: `2 ^ (t - 2) = 2`, the forms `x² + 15y²` and `3x² + 5y²`.
example : {q : ℤ × ℤ × ℤ | IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = -60 ∧
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
    (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)}.ncard = 2 := by
  have h := (ncard_ambiguous_reduced_forms 60 (by norm_num) (by norm_num)).2.1 (by norm_num)
  simpa [Nat.primeFactors, Nat.primeFactorsList_ofNat] using h

-- `d = 32 ≡ 0 (mod 32)`: `2 ^ t = 2`, the forms `x² + 8y²` and `3x² + 2xy + 3y²`.
example : {q : ℤ × ℤ × ℤ | IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = -32 ∧
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
    (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)}.ncard = 2 := by
  have h := (ncard_ambiguous_reduced_forms 32 (by norm_num) (by norm_num)).2.2 (by norm_num)
  simpa [Nat.primeFactors, Nat.primeFactorsList_ofNat] using h

end BinaryQuadraticForm.AmbiguousReducedFormsTest
