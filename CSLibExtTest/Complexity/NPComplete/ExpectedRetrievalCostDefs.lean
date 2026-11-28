/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ExpectedRetrievalCostDefs

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ExpectedRetrievalCostInstance) :
    expectedRetrievalCostDec (bitEncode i) = true ↔
      WellFormed i ∧ ExpectedRetrievalCostFeasible i := by
  simp [expectedRetrievalCostDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : expectedRetrievalCostDec [true] = false := by
  have h : bitDecode (α := ExpectedRetrievalCostInstance) [true] = none := rfl
  simp [expectedRetrievalCostDec, h]

/-- Two records of probability `1/2` in two sectors: only the latencies `d(0, 0) = d(1, 1) = 1`
count, for expected cost `1/4 + 1/4 = 1/2 ≤ 1`. -/
example : expectedRetrievalCostDec
    (bitEncode (([(1, 2), (1, 2)], 2, 1) : ExpectedRetrievalCostInstance)) = true :=
  (accepts_encoding _).2 ⟨by unfold WellFormed; decide +kernel, fun r => r,
    fun j => ⟨j, rfl⟩, by decide +kernel⟩

/-- Four records of probability `1/4` in four sectors: every surjective allocation puts one
record in each sector, and the expected cost is `(12 + 12) / 16 = 3/2 > 1`. -/
example : expectedRetrievalCostDec
    (bitEncode (([(1, 4), (1, 4), (1, 4), (1, 4)], 4, 1) : ExpectedRetrievalCostInstance)) =
      false := by
  have h : ¬ ExpectedRetrievalCostFeasible
      (([(1, 4), (1, 4), (1, 4), (1, 4)], 4, 1) : ExpectedRetrievalCostInstance) := by
    unfold ExpectedRetrievalCostFeasible
    decide +kernel
  simp [expectedRetrievalCostDec, bitDecode_bitEncode, h]

/-- One record cannot fill two sectors, so no allocation has every sector nonempty. -/
example : expectedRetrievalCostDec
    (bitEncode (([(1, 1)], 2, 1) : ExpectedRetrievalCostInstance)) = false := by
  have h : ¬ ExpectedRetrievalCostFeasible (([(1, 1)], 2, 1) : ExpectedRetrievalCostInstance) :=
    fun ⟨f, hf, _⟩ => by
      obtain ⟨a, ha⟩ := hf ⟨0, by decide⟩
      obtain ⟨b, hb⟩ := hf ⟨1, by decide⟩
      have : a = b := Fin.ext (by
        have ha' : a.1 < 1 := a.2
        have hb' : b.1 < 1 := b.2
        omega)
      subst this
      exact absurd (ha.symm.trans hb) (by decide)
  simp [expectedRetrievalCostDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost
