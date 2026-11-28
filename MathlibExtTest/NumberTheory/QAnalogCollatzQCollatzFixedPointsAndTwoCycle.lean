/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QAnalogCollatzQCollatzFixedPointsAndTwoCycle

/-!
# Tests for fixed points and the two-cycle of the q-Collatz map

Specializes the classification to parameters with fixed points `0` and `1 + X`
and nontrivial two-cycle `1`, `X`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Lemma 13 (`jis-2025-25.6.8-lem-13`).
-/

namespace MathlibExtTest.NumberTheory.QAnalogCollatzQCollatzFixedPointsAndTwoCycle

open MetaMathlibExt PowerSeries

example (x : PowerSeries (ZMod 2)) :
    qCollatz 1 (1 + X ^ 2) x = x ↔ x = 0 ∨ x = 1 + X := by
  have hadd : (X : PowerSeries (ZMod 2)) + X = 0 := by
    ext n
    simp [CharTwo.add_self_eq_zero]
  have hfactor : (1 + X : PowerSeries (ZMod 2)) * (1 + X) = 1 + X ^ 2 := by
    calc
      (1 + X : PowerSeries (ZMod 2)) * (1 + X) = 1 + (X + X) + X ^ 2 := by ring
      _ = 1 + X ^ 2 := by rw [hadd, add_zero]
  have hquot : (1 + X ^ 2 : PowerSeries (ZMod 2)) * (1 + X)⁻¹ = 1 + X :=
    ((eq_mul_inv_iff_mul_eq (by simp)).mpr hfactor).symm
  have h := (qCollatz_fixedPoints_and_twoCycle 1 (1 + X ^ 2) (by simp) (by simp)).1 x
  simpa only [hquot] using h

example (x : PowerSeries (ZMod 2)) :
    (qCollatz 1 (1 + X ^ 2) (qCollatz 1 (1 + X ^ 2) x) = x ∧
      qCollatz 1 (1 + X ^ 2) x ≠ x) ↔ x = 1 ∨ x = X := by
  have h := (qCollatz_fixedPoints_and_twoCycle 1 (1 + X ^ 2) (by simp) (by simp)).2 x
  simpa only [PowerSeries.mul_inv_cancel (1 + X ^ 2 : PowerSeries (ZMod 2)) (by simp),
    mul_one] using h

end MathlibExtTest.NumberTheory.QAnalogCollatzQCollatzFixedPointsAndTwoCycle
