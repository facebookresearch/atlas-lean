/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.Combinatorics.Enumerative.Partition.SignedEulerProduct

open PowerSeries MetaMathlibExt

-- Recover the source's quotient using the inverse of the denominator with constant term one.
example : rescale (-1) (qEulerProduct 1) =
    qEulerProduct 2 ^ 3 * invOfUnit (qEulerProduct 1 * qEulerProduct 4) 1 := by
  have h : constantCoeff (qEulerProduct 1 * qEulerProduct 4) = (1 : ℤˣ) := by
    simp [constantCoeff_qEulerProduct (k := 1) (by decide),
      constantCoeff_qEulerProduct (k := 4) (by decide)]
  rw [← rescale_neg_one_qEulerProduct_identity, mul_assoc (rescale _ _), mul_assoc,
    mul_invOfUnit _ _ h, mul_one]
