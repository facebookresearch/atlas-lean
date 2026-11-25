/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.RingTheory.PowerSeries.SeriesDivisorPowRecursion

open PowerSeries MetaMathlibExt

-- In characteristic two the square of the geometric series has no odd-degree terms.
example (k : ℕ) :
    coeff (2 * k + 1) (PowerSeries.mk (fun _ ↦ (1 : ZMod 2)) ^ 2) = 0 := by
  let A := PowerSeries.mk (fun _ ↦ (1 : ZMod 2))
  have hA (n : ℕ) : (n : ZMod 2) * coeff n A =
      ∑ j ∈ Finset.Icc 1 n, 1 * coeff (n - j) A := by
    simp [A, Nat.card_Icc]
  have htwo : (2 : ZMod 2) = 0 := by decide
  simpa [Nat.cast_add, Nat.cast_mul, htwo] using
    series_divisor_pow_recursion A (fun _ ↦ 1) hA 2 (2 * k + 1)
