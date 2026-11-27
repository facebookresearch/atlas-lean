/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.DeltaRing
import Mathlib.Tactic.NormNum

/-!
# Tests for δ-rings

On `ℤ` the unique `δ`-structure is `δ n = (n - n ^ p) / p`, so `δ 2 = -1` and `δ 3 = -3` for
`p = 2`, its Frobenius lift is the identity, and the sum correction of `δ` is the integral
polynomial `(x ^ p + y ^ p - (x + y) ^ p) / p`, here `-2xy`.
-/

open MathlibExt.RingTheory

example : DeltaRing.delta 2 (2 : ℤ) = -1 := by
  rw [DeltaRing.delta_int]
  norm_num

example : DeltaRing.delta 2 (3 : ℤ) = -3 := by
  rw [DeltaRing.delta_int]
  norm_num

example (n : ℤ) : DeltaRing.frobenius 2 ℤ n = n := by
  rw [DeltaRing.frobenius_int, RingHom.id_apply]

/-- For `p = 2` the sum correction is `-2xy`, and `p` times it is `x ^ 2 + y ^ 2 - (x + y) ^ 2`. -/
example (x y : ℤ) : DeltaRing.addCorrection 2 x y = -(x * y) := by
  have h : ((2 : ℕ) : ℤ) * DeltaRing.addCorrection 2 x y = x ^ 2 + y ^ 2 - (x + y) ^ 2 :=
    DeltaRing.natCast_mul_addCorrection x y
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
  push_cast at h
  rw [h]
  ring

/-- `δ` of a sum on `ℤ`, as forced by the sum rule. -/
example : DeltaRing.delta 2 ((2 : ℤ) + 3) =
    DeltaRing.delta 2 (2 : ℤ) + DeltaRing.delta 2 3 + DeltaRing.addCorrection 2 (2 : ℤ) 3 := by
  rw [DeltaRing.delta_add]
