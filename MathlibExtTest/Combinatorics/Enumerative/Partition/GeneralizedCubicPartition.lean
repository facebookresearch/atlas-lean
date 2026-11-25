/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.GeneralizedCubicPartition
import MathlibExt.Combinatorics.Enumerative.PentagonalNumber

open MetaMathlibExt PowerSeries

-- Truncated subtraction makes zero colors give the same series as one color.
example : generalizedCubicPartitionSeries 0 = generalizedCubicPartitionSeries 1 := rfl

-- With one color the coefficients count ordinary partitions in every degree.
example (n : ℕ) : generalizedCubicPartitionCount 1 n = (partitionFunction n : ℤ) := by
  let A := mk (generalizedCubicPartitionCount 1)
  let P := mk (fun k ↦ (partitionFunction k : ℤ))
  have hA : pentagonalSeries ℤ * A = 1 := by
    simpa [A, qEulerProduct_one] using generalizedCubicPartitionCount_generatingFunction 1
  have hP : P * pentagonalSeries ℤ = 1 := mk_partitionFunction_mul_pentagonalSeries
  have he : A = P := by linear_combination P * hA - A * hP
  simpa [A, P] using congrArg (coeff n) he

-- Both progressions include their initial term.
example : (7 : ℤ) ∣ generalizedCubicPartitionCount 3 4 ∧
    (11 : ℤ) ∣ generalizedCubicPartitionCount 5 10 :=
  generalizedCubicPartitionCount_seven_eleven 0
