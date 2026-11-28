/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BinPackingFixedBinsDefs

namespace MetaMathlibExt.Complexity.NPComplete.BinPackingFixedBins

open MetaMathlibExt.BitstringEncoding

/-- Positive item sizes and a positive capacity make a well-formed instance. -/
example : WellFormed ([1, 2], 3) := by unfold WellFormed; decide

/-- The empty item list with a positive capacity is well formed. -/
example : WellFormed ([], 1) := by unfold WellFormed; decide

/-- An item of size `0` makes the instance malformed. -/
example : ¬ WellFormed ([0, 1], 1) := by unfold WellFormed; decide

/-- A capacity of `0` makes the instance malformed. -/
example : ¬ WellFormed ([1], 0) := by unfold WellFormed; decide

/-- `withBins` appends the fixed number of bins to the BIN PACKING instance. -/
example : withBins ([1, 2], 3) 2 = (([1, 2], 3, 2) : BinPacking.BinPackingInstance) := rfl

/-- Two items of size `2` fit into two bins of capacity `2`. -/
example : binPackingFixedBinsDec 2 (bitEncode (α := BinPackingFixedBinsInstance) ([2, 2], 2)) =
    true := by
  classical
  rw [binPackingFixedBinsDec, bitDecode_bitEncode, decide_eq_true_eq]
  refine ⟨by unfold WellFormed; decide, [[2], [2]], rfl, by simp [withBins], ?_⟩
  simp [withBins]

/-- The same items do not fit into one bin of capacity `2`: the fixed `K` is the number of bins
asked about. -/
example : binPackingFixedBinsDec 1 (bitEncode (α := BinPackingFixedBinsInstance) ([2, 2], 2)) =
    false := by
  rw [binPackingFixedBinsDec, bitDecode_bitEncode, decide_eq_false_iff_not]
  rintro ⟨-, bins, hlen, hperm, hsum⟩
  obtain ⟨b, rfl⟩ : ∃ b, bins = [b] := List.length_eq_one_iff.mp hlen
  have hb : b.sum = 4 := by simpa [withBins] using hperm.sum_eq
  have := hsum b (by simp)
  change b.sum ≤ 2 at this
  omega

/-- An item of size `0` is rejected although it fits into any bin. -/
example : binPackingFixedBinsDec 2 (bitEncode (α := BinPackingFixedBinsInstance) ([0], 1)) =
    false := by
  rw [binPackingFixedBinsDec, bitDecode_bitEncode, decide_eq_false_iff_not]
  rintro ⟨hwf, -⟩
  exact absurd (hwf.1 0 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.BinPackingFixedBins
