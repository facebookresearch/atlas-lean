/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.PondPendPartitions

open MetaMathlibExt PowerSeries

-- Both counts include the empty partition. Only PEND permits the single part of size one.
example : pendCount 0 = 1 ∧ pondCount 0 = 1 := by decide

example : pendCount 1 = 1 ∧ pondCount 1 = 0 := by
  simp [pendCount, pondCount, IsPendParts, IsPondParts]

-- Repeating one even part cannot compensate for a different even part occurring just once.
example : IsPendParts {1, 2, 2, 2, 4, 4} ∧ ¬ IsPendParts {1, 2, 2, 2, 4} := by decide

-- Taking a coefficient gives the corresponding convolution identity over the integers.
example (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      coeff ij.1 (qEulerProduct 1 * qEulerProduct 4 * qEulerProduct 6) *
        (pendCount ij.2 : ℤ)) =
      coeff n (qEulerProduct 2 * qEulerProduct 12) := by
  simpa only [coeff_mul, coeff_mk] using congrArg (coeff n) pendCount_generatingFunction
