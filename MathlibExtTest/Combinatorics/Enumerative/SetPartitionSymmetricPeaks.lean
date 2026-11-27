/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SetPartitionSymmetricPeaks

open Finset PowerSeries MetaMathlibExt

namespace MathlibExtTest.SetPartitionSymmetricPeaks

private noncomputable def partitions (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ((univ.filter fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w).card : ℤ)

private noncomputable def peakTotals (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ((∑ w ∈ univ.filter
    (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    symmetricPeakCount (List.ofFn fun i => (w i : ℕ)) : ℕ) : ℤ)

-- The unique empty partition contributes no peaks.
example : coeff 0 (partitions 0) = 1 ∧ peakTotals 0 = 0 := by
  constructor
  · rw [partitions, coeff_mk]
    decide
  · simpa [peakTotals] using symmetricPeaks_derivative_generatingFunction 0

-- At length five the two-block formula includes both peaks of the word 01010.
example : coeff 5 (X * partitions 2 + partitions 2 *
    (X ^ 3 * invOfUnit (1 - 2 * X) 1)) = 8 := by
  have h : peakTotals 2 = X * partitions 2 + partitions 2 *
      (X ^ 3 * invOfUnit (1 - 2 * X) 1) := by
    have hI : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    simpa [peakTotals, partitions, hI] using symmetricPeaks_derivative_generatingFunction 2
  rw [← h, peakTotals, coeff_mk]
  decide

end MathlibExtTest.SetPartitionSymmetricPeaks
