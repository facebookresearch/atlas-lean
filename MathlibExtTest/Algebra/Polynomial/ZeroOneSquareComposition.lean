/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import MathlibExt.Algebra.Polynomial.ZeroOneSquareComposition

/-! # Tests for square compositions of zero-one polynomials -/

namespace MathlibExtTest.ZeroOneSquareComposition

open Polynomial MathlibExt.Algebra.PalindromicZeroOneWanted

example : ¬ IsZeroOnePoly (X ^ 2 + C (2 : ℤ)) := by
  intro h
  simpa [coeff_add, coeff_X_pow] using h 0

-- The square composition of the third cyclotomic polynomial factors over the integers.
example :
    ((cyclotomic 3 ℤ).comp (X ^ 2)).map (Int.castRingHom (ZMod 4)) =
      (cyclotomic 3 ℤ * (cyclotomic 3 ℤ).comp (-X)).map (Int.castRingHom (ZMod 4)) := by
  have hirr₃ := cyclotomic.irreducible (n := 3) (by decide)
  have hirr₆ := cyclotomic.irreducible (n := 6) (by decide)
  apply map_comp_sq_eq_mul (hirr := hirr₃)
  · intro n
    rcases n with _ | _ | _ | n <;>
      simp [cyclotomic_three, coeff_X_pow, coeff_X, coeff_one]
  · simp [cyclotomic_three, coeff_X_pow]
  · intro hirr
    have hfactor : (cyclotomic 3 ℤ).comp (X ^ 2) = cyclotomic 6 ℤ * cyclotomic 3 ℤ := by
      simpa only [expand_eq_comp_X_pow] using
        cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two (n := 3) (by decide) ℤ
    exact (hirr.isUnit_or_isUnit hfactor).elim hirr₆.not_isUnit hirr₃.not_isUnit

end MathlibExtTest.ZeroOneSquareComposition
