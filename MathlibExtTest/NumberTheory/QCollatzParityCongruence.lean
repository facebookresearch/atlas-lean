/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QCollatzParityCongruence

/-! # Tests for congruence of q-Collatz parity vectors -/

open MetaMathlibExt PowerSeries

-- A first disagreement at degree two is invisible modulo 4.
example : PadicInt.toZModPow 2 (qCollatzParityVector (1 + X) 1 (X + X ^ 2)) =
    PadicInt.toZModPow 2 (qCollatzParityVector (1 + X) 1 X) := by
  apply (qCollatzParityVector_modEq_iff (1 + X) 1 (by simp) (by simp) 1 _ _).mpr
  simp

-- The same disagreement is visible modulo 8.
example : PadicInt.toZModPow 3 (qCollatzParityVector (1 + X) 1 (X + X ^ 2)) ≠
    PadicInt.toZModPow 3 (qCollatzParityVector (1 + X) 1 X) := by
  intro h
  have hd := (qCollatzParityVector_modEq_iff (1 + X) 1 (by simp) (by simp) 2 _ _).mp h
  have hc := X_pow_dvd_iff.mp hd 2 (by decide)
  simp [coeff_X_pow] at hc

-- Identical inputs agree at the base precision.
example (a : PowerSeries (ZMod 2)) : (X : PowerSeries (ZMod 2)) ^ (0 + 1) ∣ a - a :=
  (qCollatzParityVector_modEq_iff 1 1 (by simp) (by simp) 0 a a).mp rfl
