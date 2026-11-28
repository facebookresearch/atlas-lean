/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QCollatzParityFlip

/-! # Tests for parity of perturbed q-Collatz iterates -/

open MetaMathlibExt PowerSeries

-- At iterate zero the map is the identity, and the odd summand already flips parity.
example (U V : PowerSeries (ZMod 2)) (hV : constantCoeff V ≠ 0) :
    constantCoeff (U + V) ≠ constantCoeff U := by
  simpa only [Function.iterate_zero_apply, pow_zero, one_mul] using
    qCollatz_iterate_parity_flip (A := 1) (B := 1) (hA := by simp) (hB := by simp)
      (n := 0) (U := U) (V := V) (hV := hV)

-- Both inputs start even and reach the odd branch on their second step.
example :
    constantCoeff ((qCollatz (1 + X) 1)^[2] (X + X ^ 2)) ≠
      constantCoeff ((qCollatz (1 + X) 1)^[2] X) := by
  simpa only [mul_one] using
    qCollatz_iterate_parity_flip (A := 1 + X) (B := 1) (hA := by simp) (hB := by simp)
      (n := 2) (U := X) (V := 1) (hV := by simp)
