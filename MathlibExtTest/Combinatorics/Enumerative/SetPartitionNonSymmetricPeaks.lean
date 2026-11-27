/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SetPartitionNonSymmetricPeaks

open Finset PowerSeries MetaMathlibExt

namespace MathlibExtTest.SetPartitionNonSymmetricPeaks

example : nonSymmetricPeakCount [] = 0 ∧ nonSymmetricPeakCount [0, 1] = 0 := by decide

example : nonSymmetricPeakCount [0, 2, 0] = 0 ∧ nonSymmetricPeakCount [0, 2, 1, 3, 0] = 2 := by
  decide

private noncomputable def partitions (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ((univ.filter fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w).card : ℤ)

private noncomputable def peakTotals (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ((∑ w ∈ univ.filter
    (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    nonSymmetricPeakCount (List.ofFn fun i => (w i : ℕ)) : ℕ) : ℤ)

-- The only peaks possible with two labels have equal neighbors.
example : peakTotals 2 = 0 := by
  have hI : Icc 3 2 = (∅ : Finset ℕ) := by decide
  simpa [peakTotals, hI] using nonSymmetricPeaks_derivative_generatingFunction 2

-- With three blocks, both terms in the formula contribute at degree six.
set_option maxRecDepth 4096 in
example : coeff 6 (X * partitions 3 + partitions 3 *
    (2 * X ^ 3 * invOfUnit (1 - 3 * X) 1)) = 27 := by
  have h : peakTotals 3 = X * partitions 3 + partitions 3 *
      (2 * X ^ 3 * invOfUnit (1 - 3 * X) 1) := by
    have hI : Icc 3 3 = ({3} : Finset ℕ) := by decide
    simpa [peakTotals, partitions, hI] using nonSymmetricPeaks_derivative_generatingFunction 3
  rw [← h, peakTotals, coeff_mk]
  decide

end MathlibExtTest.SetPartitionNonSymmetricPeaks
