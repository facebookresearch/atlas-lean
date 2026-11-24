/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Height.LehmerPolynomial

/-!
# Tests for the Mahler measure bound on Lehmer's polynomial

The bound also applies after adjoining a root at zero, whose Mahler factor is one.
-/

open Polynomial MathlibExt.NumberTheory.LehmerConstant

example : intMahlerMeasure lehmerPolynomial ≤ 1176281 / 1000000 :=
  intMahlerMeasure_lehmerPolynomial_le

example : 1000000 * intMahlerMeasure (X * lehmerPolynomial) ≤ 1176281 := by
  rw [intMahlerMeasure_mul, intMahlerMeasure_X, one_mul]
  linarith [intMahlerMeasure_lehmerPolynomial_le]
