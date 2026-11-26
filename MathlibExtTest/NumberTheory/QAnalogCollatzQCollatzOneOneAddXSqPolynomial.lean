/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QAnalogCollatzQCollatzOneOneAddXSqPolynomial
import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.NumberTheory.QCollatzParityFlip

/-! # Tests for polynomial orbits of $T_{1,1+q^2}$ -/

namespace MathlibExtTest.NumberTheory.QAnalogCollatzQCollatzOneOneAddXSqPolynomial

open MetaMathlibExt PowerSeries

-- A degree-three polynomial reaches the target set after finitely many steps.
example : ∃ k : ℕ, (qCollatz 1 (1 + X ^ 2))^[k]
    (((Polynomial.X ^ 3 + Polynomial.X + 1 : Polynomial (ZMod 2))) : PowerSeries (ZMod 2)) ∈
    ({0, 1 + X, 1, X} : Set (PowerSeries (ZMod 2))) :=
  qCollatz_one_one_add_X_sq_polynomial.1 _

-- The image of a degree-three polynomial is a polynomial.
example : ∃ p : Polynomial (ZMod 2), qCollatz 1 (1 + X ^ 2)
    (((Polynomial.X ^ 3 + Polynomial.X ^ 2 : Polynomial (ZMod 2))) : PowerSeries (ZMod 2)) = p := by
  have hx : ∃ q : Polynomial (ZMod 2),
      (((Polynomial.X ^ 3 + Polynomial.X ^ 2 : Polynomial (ZMod 2))) : PowerSeries (ZMod 2)) = q :=
    ⟨_, rfl⟩
  exact (qCollatz_one_one_add_X_sq_polynomial.2 _).mpr hx

-- A multiple of `X` by a degree-two polynomial is a polynomial since its image is.
example : ∃ q : Polynomial (ZMod 2), (X : PowerSeries (ZMod 2)) *
    (((Polynomial.X ^ 2 + 1 : Polynomial (ZMod 2))) : PowerSeries (ZMod 2)) = q := by
  have hT : ∃ p : Polynomial (ZMod 2), qCollatz 1 (1 + X ^ 2)
      ((X : PowerSeries (ZMod 2)) *
        (((Polynomial.X ^ 2 + 1 : Polynomial (ZMod 2))) : PowerSeries (ZMod 2))) = p := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_⟩
    rw [qCollatz_X_mul]
  exact (qCollatz_one_one_add_X_sq_polynomial.2 _).mp hT

end MathlibExtTest.NumberTheory.QAnalogCollatzQCollatzOneOneAddXSqPolynomial
